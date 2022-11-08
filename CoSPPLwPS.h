/*
    Implementation of the Algorithm (Algorithm 1) for Paper: 
        Coordination of Single Pulsed Power Load with Power Source (CoSPPLwPS)
        Problem with constant normal load functions
*/
#include <iostream>
#include <iomanip>
#include <vector>
#include <algorithm>
#include <random>
#include <chrono>
#include <ctime>
#include <float.h> 
#include <math.h>

using namespace std::chrono; 
using namespace std;

/*
    Data Structures for Schedules 
*/
// Time-based Representation
struct Itemt{
    char type;
    // (type = 'D') deployment start time, number of pulses: 
    int td, S; // type = 'Deployment'
    // (type = 'C') charging time parameters t_1, t_2, t_3, t_4, max charging power
    int t_1; double t_2, t_3; int t_4; double P; // type = 'Charging'

    Itemt(char type, int td, int S): type(type), td(td), S(S) {}
    Itemt(char type, int t_1, double t_2, double t_3, int t_4, double P): 
          type(type), t_1(t_1), t_2(t_2), t_3(t_3), t_4(t_4), P(P) {}
    
    void print(){
        cout << type << ": ";
        if( type == 'C' ){
            cout << "(" << t_1 << ", " << t_2 << ", " << t_3 << ", " << t_4 << ", " << P << ")";
        }else{
            cout << "(" << td << ", " << S << ")";
        }
        cout << endl;
    }
};

// Action-based Representation
struct Itema{
    char type;
    // (type = 'D') number of pulses: 
    int S;
    // (type = 'C') charging duration:
    int duration;

    Itema(char type, int val) : type(type) {
        if(type == 'D') S = val;
        else duration = val; // type == 'C'
    }

    void print(){
        cout << type << ": ";
        if( type == 'C' ) cout << duration;
        else cout << S;
        cout << endl;
    }
};

/* 
    Optimal schedule for Problem with constant normal load function
*/
struct ScheduleConstantNL{
    /* Problem Parameters */
    // (Deployment) max PPL power, width of PPL pulse, time between two consecutive pulses: 
    double P_d; int Dtu, Dtl;
    // (Energy bounds) initial energy, energy lower bound, energy upper bound: 
    double E_0, E_min, E_max;
    // (Available energy) normal load function, max total power: 
    double P_NL, P_Gmax;
    // (Charging) ramp-up rate limit, ramp-down rate limit, charging rate upper bound: 
    double R_u, R_d, P_cmax;
    // (Deployment & Charging) min time between a charging process and a deployment process: 
    int DT_min;
    
    // (Input) studied time: 
    int T;
    
    /* Intermediate Variables */
    double P_climit;    // P_climit = min { P_cmax , P_Gmax - P_NL } 

    /* DP Variables */
    double** F_1;       // State Variables for F_1
    double** F_2;       // State Variables for F_2
    int S_MAX;          // Optimal Objective Value

    // Optimal Schedule Variables 
    

    ScheduleConstantNL( double P_d, int Dtu, int Dtl, 
                        double E_0, double E_min, double E_max,
                        double P_NL, double P_Gmax,
                        double R_u, double R_d, double P_cmax,
                        int DT_min ) : 
                        P_d(P_d), Dtu(Dtu), Dtl(Dtl), 
                        E_0(E_0), E_min(E_min), E_max(E_max),
                        P_NL(P_NL), P_Gmax(P_Gmax), 
                        R_u(R_u), R_d(R_d), P_cmax(P_cmax), 
                        DT_min(DT_min) {
                           P_climit = min(P_cmax, P_Gmax - P_NL);
                        }
    
    ScheduleConstantNL( ) {}

    void setT(int studiedTime){
        T = studiedTime;
    }

    double E_CtL(double Dt){ // The input should be integer
        double harmonicmeanR = (2 * R_u * R_d)/(R_u + R_d);
        if( Dt < P_climit/(harmonicmeanR/2) ){
            return ((Dt*Dt) * harmonicmeanR)/4;
        }else{
            return P_climit * Dt - (P_climit*P_climit)/harmonicmeanR;
        }
    }

    double rE_CtL(double E){ // Inverse of E_CtL
        double harmonicmeanR = (2 * R_u * R_d)/(R_u + R_d);
        if( E < (P_climit*P_climit)/harmonicmeanR ){
            return sqrt( (4 * E) / harmonicmeanR );
        }else{
            return E/P_climit + P_climit/harmonicmeanR;
        }
    }

    Itemt CtLwLE(int t_1, int Dt, double DE_m){
        /* Inputs: charging start time, duartion, max energy charge-able */
        double t_2, t_3; int t_4; double P;
        double halfHarmonicmeanR = (R_u * R_d)/(R_u + R_d);
        if( E_CtL(Dt) <= DE_m ){
            if( Dt >= P_climit/halfHarmonicmeanR ){
                P = P_climit;
            }else{
                P = Dt * halfHarmonicmeanR;
            }
        }else{
            P = ( Dt - sqrt(Dt*Dt - 2*DE_m/halfHarmonicmeanR) ) * halfHarmonicmeanR;
        }
        t_4 = t_1 + Dt, t_2 = t_1 + P/R_u, t_3 = t_4 - P/R_d;
        return Itemt('C', t_1, t_2, t_3, t_4, P);
    }

    vector<Itema> ActionBasedScheudle(){ // Use Computed F_1, F_2, S_MAX
        vector<Itema> St;
        if(S_MAX == 0) {
            Itema chargingAction('C', T);
            St.push_back(chargingAction);
            return St;
        }

        int F, t, S; // Current DP State 
        if( T-Dtu >= 0 && S_MAX-1 >= 0 && F_1[T-Dtu][S_MAX-1] - P_d*Dtu >= E_min ){
            F = 1, t = T-Dtu, S = S_MAX - 1;
        }else{
            F = 2, t = T, S = S_MAX;
        }

        // Auxiliary Variables
        int Dt_dmax = ceil(rE_CtL(E_max - E_min));

        while( true ){
            if( F == 1 ){
                if( St.empty() || St.back().type != 'D' ){
                    Itema deploymentAction('D', 1);
                    St.push_back(deploymentAction);
                }else{
                    St.back().S ++;
                }
            }else{ // F == 2
                // Compute the duration of the charging process
                int duration; 
                if(S >= 1){
                    double maxF2 = -1;
                    for(int Dt = 1; Dt <= Dt_dmax; Dt++){
                        int Dt_c = (t < T) ? max(Dt, DT_min) : Dt;
                        int prevt = t - Dt_c - Dtu;
                        if(prevt < 0) break; 
                        // prevt >= 0:
                        double remainEnergy = F_1[prevt][S-1] - P_d * Dtu;
                        if(remainEnergy < E_min) break;
                        // remainEnergy >= E_min:
                        double candidateF2 = min(E_max, remainEnergy + E_CtL(Dt));
                        if(candidateF2 > maxF2){
                            maxF2 = candidateF2;
                            duration = Dt_c; // duration = Dt -> duration = Dt_c
                        }
                    }
                }else{ // S == 0
                    duration = t;
                }
                Itema chargingAction('C', duration);
                St.push_back(chargingAction);
            }

            if( S == 0 ){   // Loop termination condition
                if( t > 0 ){
                    Itema chargingAction('C', t);
                    St.push_back(chargingAction);
                }
                break;
            } 

            if( F == 1 ){
                if( t-Dtu-Dtl >= 0 && F_1[t-Dtu-Dtl][S-1] - P_d*Dtu >= F_2[t][S] ){
                    F = 1, t = t - Dtu - Dtl, S = S - 1;
                }else{
                    F = 2, t = t, S = S;
                }
            }else{ // F == 2
                int duration = St.back().duration;
                int Dt_c = (t < T) ? max(duration, DT_min) : duration;
                F = 1, t = t - Dt_c - Dtu, S = S - 1;
            }
        }

        reverse(St.begin(), St.end());
        return St;
    }

    vector<Itemt> ActionBasedToTimeBased(vector<Itema> St){
        vector<Itemt> schedule;

        int C = 0, D = 0, t = 0;
        double E_c = E_0;

        for( Itema a: St ){
            if( a.type == 'C' ){
                C = C + 1;
                int t_1 = t;
                Itemt chargingAction = CtLwLE(t_1, a.duration, E_max - E_c);
                schedule.push_back(chargingAction);
                E_c = min(E_max, E_c + E_CtL(a.duration));
                if( C == 1 || chargingAction.t_4 == T ){
                    t = t + a.duration;
                }else{
                    t = t + max(a.duration, DT_min);
                }
            }else{
                D = D + 1;
                Itemt deploymentAction('D', t, a.S);
                schedule.push_back(deploymentAction);
                E_c = E_c - a.S * P_d * Dtu;
                t = t + a.S * (Dtu + Dtl) - Dtl;
            }
        }

        return schedule;
    }

    vector<Itemt> DP(){ // Return an optimal schedule in Time-based representation
        int S_max = (T + Dtl + Dtu + Dtl - 1) / (Dtu + Dtl);
        F_1 = new double*[T+1]; for(int t = 0; t <= T; t++) F_1[t] = new double[S_max+1];
        F_2 = new double*[T+1]; for(int t = 0; t <= T; t++) F_2[t] = new double[S_max+1];

        // Initialization of all F_1, F_2
        for(int t = 0; t <= T; t++) for(int S = 0; S <= S_max; S++) {
            F_1[t][S] = F_2[t][S] = -1;
        }

        int Dt_dmax = ceil(rE_CtL(E_max - E_min));
        for(int t = 0; t <= T; t++){
            F_2[t][0] = min(E_0 + E_CtL(t), E_max);
            if(F_2[t][0] >= E_min + P_d * Dtu){
                F_1[t][0] = F_2[t][0];
            }else{
                F_1[t][0] = -1;
            }
        }
        for(int t = 0; t <= T; t++){
            for(int S = 1; S <= S_max; S++){
                // Compute F_2[t][S]
                double f2 = -1;
                for(int Dt = 1; Dt <= Dt_dmax; Dt++){
                    int Dt_c = (t < T) ? max(Dt, DT_min) : Dt;
                    int prevt = t - Dt_c - Dtu;
                    if(prevt < 0) break; 
                    // prevt >= 0:
                    double remainEnergy = F_1[prevt][S-1] - P_d * Dtu;
                    if(remainEnergy < E_min) break;
                    // remainEnergy >= E_min: 
                    double candidateF2 = min(E_max, remainEnergy + E_CtL(Dt));
                    f2 = max(f2, candidateF2);
                }
                F_2[t][S] = f2;
                // Compute F_1[t][S]
                if(t <= max(0, T - Dtu)){
                    double f1 = F_2[t][S];
                    if( t-Dtu-Dtl >= 0 && F_1[t-Dtu-Dtl][S-1] - P_d*Dtu >= E_min ){
                        f1 = max(f1, F_1[t-Dtu-Dtl][S-1] - P_d*Dtu);
                    }
                    F_1[t][S] = f1;
                    if(F_1[t][S] < E_min + P_d*Dtu){
                        F_1[t][S] = -1;
                    }
                }
            }
        }

        // Retrieve the optimal objective value S_MAX
        S_MAX = 0;
        for(int S_m = 1; S_m <= S_max; S_m++){
            if(T - Dtu >= 0 && F_1[T - Dtu][S_m] - P_d*Dtu >= E_min) S_MAX = 1 + S_m;
        }
        for(int S_m = 1; S_m <= S_max; S_m++){
            if(F_2[T][S_m] >= E_min) S_MAX = max(S_MAX, S_m);
        }
        // Trace ActionBasedScheudle
        vector<Itema> actionBasedScheudle = ActionBasedScheudle();
        // Convert to TimeBased Representation
        vector<Itemt> timeBasedSchedule = ActionBasedToTimeBased(actionBasedScheudle);

        // Print out DP states
        // F1
        cout << setw(3) << " " << "  ";
        for(int S = 0; S <= S_max; S++) {
            cout << setw(5) << S;
        }
        cout << endl;
        for(int t = 0; t <= T; t++) {
            cout << setw(3) << t << ": ";
            for(int S = 0; S <= S_max; S++) {
                cout << setw(5) << setprecision(3) << F_1[t][S];
            }
            cout << endl;
        }
        cout << endl;
        // F2
        cout << setw(3) << " " << "  ";
        for(int S = 0; S <= S_max; S++) {
            cout << setw(5) << S;
        }
        cout << endl;
        for(int t = 0; t <= T; t++) {
            cout << setw(3) << t << ": ";
            for(int S = 0; S <= S_max; S++) {
                cout << setw(5) << setprecision(3) << F_2[t][S];
            }
            cout << endl;
        }

        // Clean up the memory
        for(int t = 0; t <= T; t++) delete [] F_1[t]; 
        delete [] F_1;
        for(int t = 0; t <= T; t++) delete [] F_2[t];
        delete [] F_2;

        return timeBasedSchedule;
    }

    /*
        Greedy Heuristic Solution for Baseline Comparison
    */
    int GreedySolution(){ // Return the objective function of a greedy solution
        int S_Total = 0;

        double E_cur = E_0;

        // What is the energy upper bound ?
        double E_upper = min(E_max, E_min + (P_d * Dtu) * ((int) ((E_max - E_min) / (P_d * Dtu))));
        char lastAction = 'N'; // 'N' means nothing, it is otherwise 'C' or 'D'
        for(int t = 0; t < T; ){
            // Decide the action at time t
            if(lastAction != 'D' && (E_cur - E_min >= P_d * Dtu && T - t >= Dtu)){ // Deployment process
                int S_d_E = (E_cur - E_min) / (P_d * Dtu);
                int S_d_T = (T - t + Dtl) / (Dtu + Dtl);
                int S_d = min(S_d_E, S_d_T);
                // Update S_Total, E_cur, t
                S_Total = S_Total + S_d;
                E_cur = E_cur - S_d * P_d * Dtu;
                t = t + S_d * (Dtu + Dtl) - Dtl;
                lastAction = 'D';
            }else{ // Charging process
                int tc_4 = t + 1;
                for(; tc_4 <= T; tc_4++){
                    if(E_cur + E_CtL(tc_4 - t) >= E_upper) break;
                }
                // Update E_cur, t
                E_cur = min(E_max, E_cur + E_CtL(tc_4 - t));
                // Use DTmin to update
                if(t > 0){
                    t = max(tc_4, t + DT_min);
                }else{
                    // when t = 0, there is no restriction
                    t = tc_4;
                }
                lastAction = 'C';
            }
        }
        return S_Total;
    }

    void print(){
        cout << "- Problem Parameters -" << endl;
        cout << "P_d = " << P_d << ", Dtu = " << Dtu << ", Dtl = " << Dtl << endl;
        cout << "E_0 = " << E_0 << ", E_min = " << E_min << ", E_max = " << E_max << endl;
        cout << "P_NL = " << P_NL << ", P_Gmax = " << P_Gmax << endl;
        cout << "R_u = " << R_u << ", R_d = " << R_d << ", P_cmax = " << P_cmax << endl;
        cout << "DT_min = " << DT_min << endl;
        cout << "T = " << T << endl;

        cout << "- Intermediate Variables -" << endl;
        cout << "P_climit = " << P_climit << endl;

        cout << "- Other Complexity-related Values -" << endl;
        int S_max = (T + Dtl + Dtu + Dtl - 1) / (Dtu + Dtl);
        int Dt_dmax = ceil(rE_CtL(E_max - E_min));
        cout << "S_max = " << S_max << endl;
        cout << "Dt_dmax = " << Dt_dmax << endl;
        long long complexity = ((long long) T) * S_max * Dt_dmax;
        cout << "T * S_max * Dt_dmax = " << complexity << endl;
    }

    void solvePrint(){
        vector<Itemt> schedule = DP();

        cout << "==== Optimal Solution ====" << endl;
        cout << "S_MAX = " << S_MAX << endl;
        cout << "Optimal Schedule: " << endl;
        for(Itemt a: schedule){
            a.print();
        }
    }
};

/*
    Implementation of the Algorithm (Algorithm 2) for Paper: 
        Coordination of Single Pulsed Power Load with Power Source (CoSPPLwPS)
        Problem with general normal load functions
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

using namespace std;
using namespace std::chrono; 


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

    Itemt() {}
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

// Step Function to represent normal load or P_R(t)
struct StepFunction{
    vector<int> ts;     // Non-differentiable time points 
    vector<double> P;   // P[i] = P_NL(ts[i]); P_NL(t) = P_NL(ts[i]) for ts[i] <= t < ts[i+1]

    StepFunction() {}

    void addCriticalPoint(int t, double Pt){    // Add (t, P_t) to the function
        if(!ts.empty() && ts.back() >= t) return ;
        ts.push_back(t);
        P.push_back(Pt);
    }

    void print(){
        for(int i = 0; i < ts.size() - 1; i++){
            int start = ts[i], end = ts[i+1];
            cout << "P[" << start << "," << end << ") = " << P[i] << ", ";
        }
        cout << "P[" << ts.back() << ",+inf) = " << P.back();
        cout << endl;
    }
};
 
/* 
    Optimal schedule for Problem with general normal load function
*/
struct ScheduleGeneralNL{
    /* Problem Parameters */
    // (Deployment) max PPL power, width of PPL pulse, time between two consecutive pulses: 
    double P_d; int Dtu, Dtl;
    // (Energy bounds) initial energy, energy lower bound, energy upper bound: 
    double E_0, E_min, E_max;
    // (Available energy) normal load function, max total power: 
    StepFunction P_NL; // P_NL.ts[0] = 0, P_NL.ts.back() < T
    double P_Gmax;
    // (Charging) ramp-up rate limit, ramp-down rate limit, charging rate upper bound: 
    double R_u, R_d, P_cmax;
    // (Deployment & Charging) min time between a charging process and a deployment process: 
    int DT_min;
    
    // (Input) studied time: 
    int T;
    
    /* Intermediate Variables */
    StepFunction P_R;   // P_R(t) = P_Gmax - P_NL(t)
    int M_NL;           // Number of non-differentiable points
    vector<int> L, R;   // L[i], R[i] as defined in the paper
    vector<vector<double> > K_u;       // K_u(i,j) as defined in the paper
    vector<vector<double> > K_d;       // K_d(i,j) as defined in the paper

    /* DP Variables */
    vector<vector<double> > C_1;       // State Variables for C_1
    vector<vector<Itemt> >  S_C;       // Charging Sub-schedules corresponding to C_1
    vector<vector<double> >   C;       // State Variables for C
    vector<vector<double> > P_1;       // State Variables for P_1
    vector<vector<double> > P_2;       // State Variables for P_2
    int S_MAX;          // Optimal Objective Value

    // Optimal Schedule Variables 
    

    ScheduleGeneralNL( double P_d, int Dtu, int Dtl, 
                        double E_0, double E_min, double E_max,
                        StepFunction P_NL, double P_Gmax,
                        double R_u, double R_d, double P_cmax,
                        int DT_min, 
                        int studiedTime ) : 
                        P_d(P_d), Dtu(Dtu), Dtl(Dtl), 
                        E_0(E_0), E_min(E_min), E_max(E_max),
                        P_NL(P_NL), P_Gmax(P_Gmax), 
                        R_u(R_u), R_d(R_d), P_cmax(P_cmax), 
                        DT_min(DT_min), 
                        T(studiedTime) {
                            M_NL = P_NL.ts.size();
                            // Compute P_R
                            P_R.addCriticalPoint(-1, -1);
                            for(int i = 0; i < P_NL.ts.size(); i++)
                                P_R.addCriticalPoint(P_NL.ts[i], P_Gmax - P_NL.P[i]);
                            P_R.addCriticalPoint(T, -1);
                        }
    
    ScheduleGeneralNL( ) {}

    /* Functions for ComputeAllC_1 */
    void computeLR(){
        L = R = vector<int>(M_NL + 2, 0);
        // Compute L[i] for all 1 <= i <= M_NL
        for(int i = 1; i <= M_NL; i++){
            int l = i;
            while(l > 1 && P_R.P[l-1] >= P_R.P[i]) l--;
            L[i] = l;
        }
        // Compute R[i] for all 1 <= i <= M_NL
        for(int i = 1; i <= M_NL; i++){
            int r = i;
            while(r < M_NL && P_R.P[r+1] >= P_R.P[i]) r++;
            R[i] = r;
        }
    }

    void computeC_1(int i, int j){  // Compute C_1[i][j] and S_C[i][j]
        C_1[i][j] = 0; double t_2 = i, t_3 = i, P = 0;

        for(int k = 1; k <= M_NL; k++){
            if(j > P_R.ts[k] && i < P_R.ts[k+1]){   
                // When (i,j) intersects (P_R.ts[k], P_R.ts[k+1])
                int t_cl = max(P_R.ts[L[k]], i), t_cr = min(P_R.ts[R[k]+1], j);
                double P_dash = min(P_R.P[k], P_cmax);
                double k1 = K_u[i][t_cl], k2 = K_d[t_cr][j];
                double t_2_d = i + P_dash / k1, t_3_d = j + P_dash / k2;
                if(t_2_d < t_3_d){
                    double candidateC1 = (t_3_d - t_2_d + j - i) * P_dash / 2;
                    if(C_1[i][j] < candidateC1){
                        t_2 = t_2_d, t_3 = t_3_d, P = P_dash, C_1[i][j] = candidateC1;
                    }
                }else{
                    double candidateC1 = (P_dash*(i-j)*(j-i)/(t_3_d - t_2_d + i - j))/2;
                    if(C_1[i][j] < candidateC1){
                        t_2 = (i*t_3_d - j*t_2_d)/(t_3_d - t_2_d + i - j);
                        t_3 = t_2;
                        P = P_dash * (i-j) / (t_3_d - t_2_d + i - j);
                        C_1[i][j] = candidateC1;
                    }
                }
            }
        }

        S_C[i][j] = Itemt('C', i, t_2, t_3, j, P);
    }

    void ComputeAllC_1(){
        computeLR();    // Compute auxiliary variables L, R

        /* Compute K_u(i,j), K_d(i,j), for all 0 <= i <= j <= T */
        // Initialization of K_u(i,j), K_d(i,j)
        K_u = vector<vector<double> >(T+1, vector<double>(T+1, R_u));
        K_d = vector<vector<double> >(T+1, vector<double>(T+1, -R_d));

        // Computation of K_u(i,j), K_d(i,j)
        for(int i = 0; i <= T; i++) for(int j = i+1; j <= T; j++){
            for(int k = 1; k <= M_NL; k++){
                if( i < P_R.ts[k+1] && P_R.ts[k+1] <= j )
                    K_u[i][j] = min(K_u[i][j], P_R.P[k]/(P_R.ts[k+1] - i));
                if( i <= P_R.ts[k] && P_R.ts[k] < j )
                    K_d[i][j] = max(K_d[i][j], P_R.P[k]/(P_R.ts[k] - j));
            }
        }

        /* Compute All C_1, S_C */
        for(int i = 0; i <= T; i++) for(int j = i; j <= T; j++){
            computeC_1(i, j);
        }

        /* Clear memory K_u, K_d */
        K_u.clear(), K_d.clear();
    }

    /* Functions for computeAllC */

    void ComputeAllC(){
        for(int i = 0; i <= T; i++) for(int j = i; j <= T; j++) C[i][j] = 0;
        // Computation of C(i,j)
        for(int i = 0; i <= T; i++) for(int j = i+1; j <= T; j++){
            for(int k = i; k < j; k++){
                C[i][j] = max(C[i][j], C[i][k] + C_1[k][j]);
            }
        }
    }

    vector<Itemt> TraceC(int i, int j){
        vector<Itemt> CS;
        int j_d = j, k = j - 1;
        while(k >= i){
            if(C[i][j_d] == C[i][k] + C[k][j_d]){
                CS.push_back(S_C[k][j_d]);
                j_d = k;
            }
            k = k - 1;
        }
        reverse(CS.begin(), CS.end());
        return CS;
    }

    vector<Itemt> GCtLwLE(vector<Itemt> CS, double DE_m){
        vector<Itemt> CS_d;
        double E_t = 0;

        for(int i = 0; i < CS.size(); i++){
            Itemt S = CS[i];
            int t_1 = S.t_1, t_4 = S.t_4;
            double t_2 = S.t_2, t_3 = S.t_3, P = S.P;
            double E_c = P * (t_4 + t_3 - t_2 - t_1) / 2;
            if(E_t + E_c <= DE_m){
                E_t = E_t + E_c;
                CS_d.push_back(S);
            }else{
                double R_uq = P/(t_2 - t_1), R_dq = P/(t_4 - t_3);
                double Dtq  = t_4 - t_1;
                double halfHarmonicmeanR = (R_uq * R_dq)/(R_uq + R_dq);
                double P_dash = (Dtq - sqrt(Dtq*Dtq - 2*(DE_m-E_t)/halfHarmonicmeanR)) * halfHarmonicmeanR;
                double t_2_d = t_1 + P_dash/R_uq, t_3_d = t_4 - P_dash/R_dq;
                Itemt chargingAction('C', t_1, t_2_d, t_3_d, t_4, P_dash); 
                CS_d.push_back(chargingAction);
                break;
            }
        }

        return CS_d;
    }

    /* Functions for GDP */
    
    vector<Itema> GActionBasedScheudle(){ // Use Computed P_1, P_2, S_MAX
        vector<Itema> St;
        if(S_MAX == 0) {
            Itema chargingAction('C', T);
            St.push_back(chargingAction);
            return St;
        }

        int P, t, S; // Current DP State 
        if( T-Dtu >= 0 && S_MAX-1 >= 0 && P_1[T-Dtu][S_MAX-1] - P_d*Dtu >= E_min ){
            P = 1, t = T-Dtu, S = S_MAX - 1;
        }else{
            P = 2, t = T, S = S_MAX;
        }

        while( true ){
            if( P == 1 ){
                if( St.empty() || St.back().type != 'D' ){
                    Itema deploymentAction('D', 1);
                    St.push_back(deploymentAction);
                }else{
                    St.back().S ++;
                }
            }else{ // P == 2
                // Compute the duration of the charging process
                int duration; 
                if(S >= 1){
                    double maxP2 = -1;
                    for(int Dt = 1; Dt <= t - Dtu; Dt++){
                        int Dt_c = (t < T) ? max(Dt, DT_min) : Dt;
                        int prevt = t - Dt_c - Dtu;
                        if(prevt < 0) break; 
                        // prevt >= 0:
                        double remainEnergy = P_1[prevt][S-1] - P_d * Dtu;
                        if(remainEnergy < E_min) break;
                        // remainEnergy >= E_min:
                        double candidateP2 = min(E_max, remainEnergy + C[t - Dt_c][t]);
                        if(candidateP2 > maxP2){
                            maxP2 = candidateP2;
                            duration = Dt_c; // duration = Dt -> duration = Dt_c
                        }
                    }
                }else{ // S == 0
                    duration = t;
                }
                
                //cout << "P_2[" << t << "][" << S << "] -> " << duration << endl;

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

            if( P == 1 ){
                if( t-Dtu-Dtl >= 0 && P_1[t-Dtu-Dtl][S-1] - P_d*Dtu >= P_2[t][S] ){
                    P = 1, t = t - Dtu - Dtl, S = S - 1;
                }else{
                    P = 2, t = t, S = S;
                }
            }else{ // P == 2
                int duration = St.back().duration;
                int Dt_c = (t < T) ? max(duration, DT_min) : duration;
                P = 1, t = t - Dt_c - Dtu, S = S - 1;
            }
        }

        reverse(St.begin(), St.end());
        return St;
    }
    
    vector<Itemt> GActionBasedToTimeBased(vector<Itema> St){
        vector<Itemt> schedule;

        int Counter = 0, t = 0;
        double E_c = E_0;

        for( Itema a: St ){
            if( a.type == 'C' ){
                Counter = Counter + 1;

                vector<Itemt> CS = TraceC(t, t + a.duration);
                vector<Itemt> CS_d = GCtLwLE(CS, E_max - E_c);
                schedule.insert(schedule.end(), CS_d.begin(), CS_d.end());

                E_c = min(E_max, E_c + C[t][t + a.duration]);
                
                if( Counter == 1 || schedule.back().t_4 == T ){
                    t = t + a.duration;
                }else{
                    t = t + max(a.duration, DT_min);
                }
            }else{
                Itemt deploymentAction('D', t, a.S);
                schedule.push_back(deploymentAction);
                E_c = E_c - a.S * P_d * Dtu;
                t = t + a.S * (Dtu + Dtl) - Dtl;
            }
        }

        return schedule;
    }

    vector<Itemt> GDP(){
        /* Initialization of C_1, S_C, C, P_1, P_2 */
        GDP_init();
        ComputeAllC_1();
        ComputeAllC();

        int S_max = (T + Dtl + Dtu + Dtl - 1) / (Dtu + Dtl);
        // Initialization of all P_1, P_2
        for(int t = 0; t <= T; t++) for(int S = 0; S <= S_max; S++) {
            P_1[t][S] = P_2[t][S] = -1;
        }

        // Base cases of GDP
        for(int t = 0; t <= T; t++){
            P_2[t][0] = min(E_0 + C[0][t], E_max);
            if(P_2[t][0] >= E_min + P_d * Dtu){
                P_1[t][0] = P_2[t][0];
            }else{
                P_1[t][0] = -1;
            }
        }

        // General cases of GDP
        for(int t = 0; t <= T; t++){
            for(int S = 1; S <= S_max; S++){
                // Compute P_2[t][S]
                double p2 = -1;
                for(int Dt = 1; Dt <= t - Dtu; Dt++){
                    int Dt_c = (t < T) ? max(Dt, DT_min) : Dt;
                    int prevt = t - Dt_c - Dtu;
                    if(prevt < 0) break; 
                    // prevt >= 0:
                    double remainEnergy = P_1[prevt][S-1] - P_d * Dtu;
                    if(remainEnergy < E_min) break;
                    // remainEnergy >= E_min: 
                    double candidateP2 = min(E_max, remainEnergy + C[t - Dt_c][t]);
                    p2 = max(p2, candidateP2);
                }
                P_2[t][S] = p2;
                // Compute P_1[t][S]
                if(t <= max(0, T - Dtu)){
                    double p1 = P_2[t][S];
                    if( t-Dtu-Dtl >= 0 && P_1[t-Dtu-Dtl][S-1] - P_d*Dtu >= E_min ){
                        p1 = max(p1, P_1[t-Dtu-Dtl][S-1] - P_d*Dtu);
                    }
                    P_1[t][S] = p1;
                    if(P_1[t][S] < E_min + P_d*Dtu){
                        P_1[t][S] = -1;
                    }
                }
            }
        }

        // Retrieve the optimal objective value S_MAX
        S_MAX = 0;
        for(int S_m = 1; S_m <= S_max; S_m++){
            if(T - Dtu >= 0 && P_1[T - Dtu][S_m] - P_d*Dtu >= E_min) S_MAX = 1 + S_m;
        }
        for(int S_m = 1; S_m <= S_max; S_m++){
            if(P_2[T][S_m] >= E_min) S_MAX = max(S_MAX, S_m);
        }

        // Trace ActionBasedScheudle
        vector<Itema> actionBasedScheudle = GActionBasedScheudle();
        // Convert to TimeBased Representation
        vector<Itemt> timeBasedSchedule = GActionBasedToTimeBased(actionBasedScheudle);
        /* Clean up dynamic allocated memory for C_1, S_C, C, P_1, P_2 */
        GDP_cleanup();

        return timeBasedSchedule;
    }

    void GDP_init(){
        /* Initialization of C_1, S_C, C, P_1, P_2 */
        // Initialization of C_1, S_C
        C_1 = vector<vector<double> >(T+1, vector<double>(T+1));
        S_C = vector<vector<Itemt> >(T+1, vector<Itemt>(T+1));
        // Initialization of C(i,j)
        C = vector<vector<double> >(T+1, vector<double>(T+1));
        // Initialization of P_1(i,j), P_2(i,j)
        int S_max = (T + Dtl + Dtu + Dtl - 1) / (Dtu + Dtl);
        P_1 = vector<vector<double> >(T+1, vector<double>(S_max+1));
        P_2 = vector<vector<double> >(T+1, vector<double>(S_max+1));
    }

    void GDP_cleanup(){
        /* Clean up dynamic allocated memory for C_1, S_C, C, P_1, P_2 */
        // Clean up for C_1, S_C
        C_1.clear(), S_C.clear();
        // Clean up for C
        C.clear();
        // Clean up for P_1, P_2
        P_1.clear(), P_2.clear();
    }

    /*
        Greedy Heuristic Solution for Baseline Comparison
    */
    int GreedySolution(){ // Return the objective function of a greedy solution
        /* Initialization of C_1, S_C, C, P_1, P_2 */
        GDP_init();
        ComputeAllC_1();
        ComputeAllC();

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
                //cout << "D: (" << t << ", " << S_d << "), ";
                // Update S_Total, E_cur, t
                S_Total = S_Total + S_d;
                E_cur = E_cur - S_d * P_d * Dtu;
                t = t + S_d * (Dtu + Dtl) - Dtl;
                lastAction = 'D';
            }else{ // Charging process
                int tc_4 = t + 1;
                for(; tc_4 <= T; tc_4++){
                    if(E_cur + C[t][tc_4] >= E_upper) break;
                    //if(E_cur + E_CtL(tc_4 - t) >= E_upper) break;
                }
                //cout << "C: (" << t << ", " << tc_4 << "), ";
                // Update E_cur, t
                E_cur = min(E_max, E_cur + C[t][tc_4]);
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
        //cout << endl;
        GDP_cleanup();

        return S_Total;
    }

    void print(){
        cout << "- Problem Parameters -" << endl;
        cout << "P_d = " << P_d << ", Dtu = " << Dtu << ", Dtl = " << Dtl << endl;
        cout << "E_0 = " << E_0 << ", E_min = " << E_min << ", E_max = " << E_max << endl;
        cout << "P_R(t): " << endl;
        P_R.print();
        //cout << "P_NL = " << P_NL << ", P_Gmax = " << P_Gmax << endl;
        cout << "R_u = " << R_u << ", R_d = " << R_d << ", P_cmax = " << P_cmax << endl;
        cout << "DT_min = " << DT_min << endl;
        cout << "T = " << T << endl;

        cout << "- Intermediate Variables -" << endl;

        cout << "- Other Complexity-related Values -" << endl;
        cout << "T = " << T << endl;
        cout << "M_NL = " << M_NL << endl;
        long long complexity = ((long long) T) * T * T + ((long long) T) * T * M_NL;
        cout << "T*T*T + T*T*M_NL = " << complexity << endl;
    }

    void solvePrint(){
        vector<Itemt> schedule = GDP();

        cout << "==== Optimal Solution ====" << endl;
        cout << "S_MAX = " << S_MAX << endl;
        cout << "Optimal Schdule: " << endl;
        for(Itemt a: schedule){
            a.print();
        }
    }
};

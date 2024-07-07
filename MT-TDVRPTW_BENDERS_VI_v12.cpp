#include <iostream>
#include <fstream>
#include <string>
#include <algorithm>
#include <ilcplex/ilocplex.h>
#include <stdio.h>
#include <ilconcert/iloexpression.h>
#include <vector>
#include <sys/stat.h>
#include <io.h>
#include <conio.h>
#include <process.h>
#include <direct.h>
#include <ctime>
#include <chrono>

//#include <iostream>
ILOSTLBEGIN

//-------------Global Variables--------------
int i, j, k, r, m, c, p, n; //indices
int imax, jmax, kmax, rmax, mmax, cmax, pmax; //number of customers, customers,vehicles,routes/vehicle,travel time periods,categories,speed periods
int Q;//Capacity of every vehicle of the homogeneous fleet
int Categories;//No of different categories of the edges
int** EdgeCat_ij;//Matrix with which category each edge belongs to
int MaxTripDuration, MaxRouteDuration;
double* BPoint_p;//breakpoints for every speed period
double** SpeedOfCatOverTime_p_c;//Matrix of how the travel time differs for every edge category in every time period
int* XCOORD_i, * YCOORD_i;//X,Y coordinates of i customer 
int* q_i;//Demand of i customer
int* e_i, * l_i;//Ready time and due date of i customer
int* s_i;//Service time of i customer
double lamda = 0.2;//required loading time at the depot as a proportion to the total service time on a trip
double f = 1, g = 0.1;//coefficients of the objective function


double** Distance_ij;//Distance Matrix between i and j
int DayDuration;//The maximum arrival time at the ending depot
double* SpeedBreakPoint_p;//the time at which the speed periods change from one to the next one
double*** Speed_ijp; //speed in p-th speed interval over arc(i,j)
double*** w_ijm; //right boundary point in m - th time interval of travel time profile over arc(i, j)
double* w_max_m; //right boundary point in m - th time interval of travel time profile over arc(i, j)
double* w_min_m; //right boundary point in m - th time interval of travel time profile over arc(i, j)
double*** TravelTime_ijm;//travel time at the m-th time intervals based on distance/speed
double*** TravelTimeCalculated_ijm;//calculated travel time at the m-th time intervals based on theta and zeta
float*** theta_ijm;//slope of travel time function between i and j in m-th breakpoint
float*** zeta_ijm;//intersection with y-axis of travel time function between i and j in m-th breakpoint

double*** TravelTimeAverage_ijm;//average travel time from i to j inside the m-th time intervals
double*** TravelTimeMinimum_ijm;//minimum travel time from i to j inside the m-th time intervals
double** TravelTimeMinimum_ij;//minimum travel time from i to j among all time intervals

int SECIterations = 0;//Number of iterations for generating SECs
int SECNumber = 0;//Total number of SEC generated


//Parameters affecting solution
double epsilon = 0.01;
double MaxBendersDuration = 3600;
int MaxNoOfMultiSol = 5;
int MinMaxNoOfMultiSol = 5;//Minimum Number of Maximum multiple solutions added per iteration
int MaxMaxNoOfMultiSol;//=2*imax, Maximum Number of Maximum multiple solutions added per iteration
int MultiFeasSolutions, MultiInfeasSolutions;
int Big_M = 1000000;//1000000
double Small_M = 0.0001;
int Big_M_bound = 1000000;
double UpperBound = Big_M;
double UpperBoundOR = Big_M;
double LowerBound = -Big_M;
double UpperBoundGlobal = Big_M;
double LowerBoundGlobal = -Big_M;
double Gap = 1;
int SolutionStatus;
double StopGapMaster = 0;//Optimality Gap to stop the code
double MinStopTime;//=imax
double StopTime;//Seconds to stop the code
double StopTimeAuxSlave;//Seconds to stop solving the auxiliary slave problem
double GapAuxSlave;//Optimality gap at the solution of auxiliary slave problem
double fraction = 0.90;
long double duration, durationPrint;  // tracks time
int start = 0, BDFeasCuts = 0, BDOptCuts = 0, AuxFeasCuts = 0, CutsPerIteration, NoOfMasterVars, NoOfSlaveVars, NoOfMasterCons, NoOfSlaveCons;

ifstream infile;
ofstream outfile, solution, solution_results, solution1, solution_results1;
char* FilePath_DataSet = "G:/Antonis/PhD_Examples/MT-TDVRPTW/MT-TDVRPTW-Small";//C:/PhD_Examples //G:/Antonis/PhD_Examples
char* FilePath_Data = "G:/Antonis/PhD_Examples/MT-TDVRPTW/MT-TDVRPTW-Small/T15-5-2";
char* FilePath_Results = "G:/Antonis/PhD_Examples/MT-TDVRPTW/MT-TDVRPTWResults-Small/T15-5-2/BENDERS_VI";//G:/Antonis/PhD_Examples
char* FilePath_Results_FileName = "BENDERS";
char FileName_DataSet[512] = "DataSet";
const int TotalNoOfProblems = 27;
int Customers[TotalNoOfProblems];
string ProblemNames[TotalNoOfProblems];
char FileName_Problem[512];

//char* FileName_Problem = "c202.txt";

//--------Construct Matrices----------------
typedef IloArray<IloNumArray> IloNumMatrix2x2;
typedef IloArray<IloNumMatrix2x2> IloNumMatrix3x3;
typedef IloArray<IloNumMatrix3x3> IloNumMatrix4x4;
typedef IloArray<IloNumMatrix4x4> IloNumMatrix5x5;

typedef IloArray<IloNumVarArray> IloNumVarMatrix2x2;
typedef IloArray<IloNumVarMatrix2x2> IloNumVarMatrix3x3;
typedef IloArray<IloNumVarMatrix3x3> IloNumVarMatrix4x4;
typedef IloArray<IloNumVarMatrix4x4> IloNumVarMatrix5x5;

typedef IloArray<IloRangeArray> IloRangeMatrix2x2;
typedef IloArray<IloRangeMatrix2x2> IloRangeMatrix3x3;
typedef IloArray<IloRangeMatrix3x3> IloRangeMatrix4x4;
typedef IloArray<IloRangeMatrix4x4> IloRangeMatrix5x5;




//--------Declare dual variables of each constraint----------------
double***** DualValueCon9_ZZZX_ijkrm;
double*** DualValueCon10a_ZZY_ikr;
double*** DualValueCon10b_ZZY_ikr;
double***** DualValueCon11a_ZX_ijkrm;
double***** DualValueCon11b_ZX_ijkrm;
double* DualValueCon12_ZZY_k;
double** DualValueCon13_ZZY_kr;
double** DualValueCon14_ZZY_kr;


//------Declare empty arrays that will host the optimal solution------
double***** X_ijkrmValue;
double**** X_ijrmValue;
double** X_ijValue;
double*** Y_ikrValue;
double** Y_irValue;
double* Y_iValue;
double*** ZZ_ikrValue;
//double***** Z_ijkrmValue;
double HetaValue = 0;

double***** OptimalX_ijkrmValue;
double*** OptimalY_ikrValue;
double*** OptimalZZ_ikrValue;
//double***** OptimalZ_ijkrmValue;
double OptimalHetaValue = 0;

double OptimalOriginalObjFunction = 0;
double OptimalMasterObjFunction = 0;
double OptimalSlaveObjFunction = 0;



vector <double> LowerBoundArray;
vector <double> UpperBoundArray;
vector <double> UpperBoundGlobalArray;
vector <double> LowerBoundGlobalArray;
vector <double> dTy;
vector <double> zCurrent;
vector <double> cTx;
vector <double> BestSlaveObjSoFar;
vector <double> Time;
vector <double> SlackValuesOfBendersCuts;
vector <double> SlackValuesOfMainMasterCons;
vector <double> NoOfCutsInEachIteration;
vector <double> NoOfCoveredVarsInEachIteration;

void Found_Error(char* name)
{
	printf("%s failed, exiting...\n", name);
	printf("Press return to continue...\n");
	getchar();
}
double InsertDataSet(char* FilePath_Data_ptr) {
	char filepath[1024];
	sprintf(filepath, "%s/%s.txt", FilePath_Data_ptr, FileName_DataSet);
	infile.open(filepath);
	/////////////////F:\Dropbox\GreenYourRoute Saharidis\GYR Saharidis\Algorithm\DATA nominal example
	//infile.open("C:/Users/zoigr/Dropbox/GYR UTH_EA/Actions/Action B2/Zoi - Action B2/TSP/3 Distance Data.txt");
	if (infile.fail()) {
		cout << "DataSet file could not be opened. Try correcting the file's location path." << endl;
		cout << filepath << endl;
		system("pause");
		exit(1);
	}
	for (int i = 0; i < TotalNoOfProblems; i++) {
		infile >> ProblemNames[i];
		//infile >> Customers[i];
	}
	infile.close();
}
int ReadTimeDepFile(char* FilePath_Data_ptr, char* FileName_ptr, char* FileName_ptr2) {
	char filepath[1024];
	sprintf(filepath, "%s/%s", FilePath_Data_ptr, FileName_ptr);
	infile.open(filepath);
	if (infile.fail()) {
		printf("%c file could not be opened. Try correcting the file's location path: %c\n", FileName_ptr, FilePath_Data_ptr);
		//cout << " file could not be opened. Try correcting the file's location path." << endl;
		//cout << filepath << endl;
		system("pause");
		exit(1);
	}
	char general[1024];

	infile >> general;
	infile >> pmax;
	infile >> general;
	infile >> cmax;
	infile >> general;
	infile >> rmax;
	if (FileName_ptr2[0] == 'c') {
		infile >> general;
		infile >> general;
		infile >> MaxTripDuration;
	}
	else {
		infile >> general;
		infile >> MaxTripDuration;
		infile >> general;
	}
	cout << "MaxTripDuration=" << MaxTripDuration << endl;
	infile >> general;
	infile >> general;
	infile >> general;
	infile >> imax;
	imax = imax + 1;
	jmax = imax;
	infile >> general;
	BPoint_p = new double[pmax];
	SpeedOfCatOverTime_p_c = new double* [pmax];
	for (int p = 0; p < pmax; p++) {
		infile >> BPoint_p[p];
		SpeedOfCatOverTime_p_c[p] = new double[cmax];
		//cout << "BPoint_p[" << p << "]=" << BPoint_p[p] << endl;
	}
	for (int p = 0; p < pmax; p++) {
		for (int c = 0; c < cmax; c++) {
			infile >> SpeedOfCatOverTime_p_c[p][c];
			//cout << "SpeedOfCatOverTime_p_c[" << p << "][" << c << "]= " << SpeedOfCatOverTime_p_c[p][c] << endl;
		}

	}

	infile.close();
	return 0;
}
int ReadCustomersFile(char* FilePath_Data_ptr, char* FileName_ptr) {
	char filepath[1024];
	sprintf(filepath, "%s/%s", FilePath_Data_ptr, FileName_ptr);
	infile.open(filepath);
	if (infile.fail()) {
		printf("%c file could not be opened. Try correcting the file's location path: %c\n", FileName_ptr, FilePath_Data_ptr);
		//cout << " file could not be opened. Try correcting the file's location path." << endl;
		//cout << filepath << endl;
		system("pause");
		exit(1);
	}
	char general[1024];
	for (int i = 0; i < 4; i++) {
		infile >> general;
	}
	infile >> kmax;
	infile >> Q;

	int imax_plus = imax + 1;
	int jmax_plus = jmax + 1;
	XCOORD_i = new int[imax_plus];
	YCOORD_i = new int[imax_plus];
	q_i = new int[imax_plus];
	e_i = new int[imax_plus];
	l_i = new int[imax_plus];
	s_i = new int[imax_plus];

	for (int i = 0; i < 12; i++) {
		infile >> general;
	}
	for (int i = 0; i < imax; i++) {
		infile >> i;
		infile >> XCOORD_i[i];
		infile >> YCOORD_i[i];
		infile >> q_i[i];
		infile >> e_i[i];
		infile >> l_i[i];
		infile >> s_i[i];
	}
	infile.close();
	//Node n+1 is the same as node 0
	XCOORD_i[imax] = XCOORD_i[0];
	YCOORD_i[imax] = YCOORD_i[0];
	q_i[imax] = q_i[0];
	e_i[imax] = e_i[0];
	l_i[imax] = l_i[0];
	s_i[imax] = s_i[0];
	return 0;
}
//int ReadInstructionsFile(char* FilePath_Data_ptr, char* FileName_ptr) {
//	char filepath[1024];
//	sprintf(filepath, "%s/%s", FilePath_Data_ptr, FileName_ptr);
//	infile.open(filepath);
//	if (infile.fail()) {
//		printf("%c file could not be opened. Try correcting the file's location path: %c\n", FileName_ptr, FilePath_Data_ptr);
//		//cout << " file could not be opened. Try correcting the file's location path." << endl;
//		//cout << filepath << endl;
//		system("pause");
//		exit(1);
//	}
//	char general[1024];
//	for (int i = 0; i < 7; i++) {
//		infile >> general;
//	}
//	infile >> MaxRouteDuration;
//	//cout << "MaxRouteDuration=" << MaxRouteDuration << endl;
//	infile >> general;
//	infile >> general;
//	infile >> kmax;
//
//	infile.close();
//	return 0;
//}
int ReadFileDouble(char* FilePath_Data_ptr, char* FileName_ptr, int sizeOne, int sizeTwo, int** Variable) {
	char filepath[1024];
	sprintf(filepath, "%s/%s", FilePath_Data_ptr, FileName_ptr);
	infile.open(filepath);
	if (infile.fail()) {
		printf("%c file could not be opened. Try correcting the file's location path: %c\n", FileName_ptr, FilePath_Data_ptr);
		//cout << " file could not be opened. Try correcting the file's location path." << endl;
		//cout << filepath << endl;
		system("pause");
		exit(1);
	}

	for (int i = 0; i < sizeOne; i++) {
		for (int j = 0; j < sizeTwo; j++) {
			infile >> Variable[i][j];
		}
	}
	infile.close();

	return 0;
}
int WriteFileSingle(char* FilePath_Data_ptr, char* FileName_ptr, int size, float* Variable) {
	char filepath[1024];
	sprintf(filepath, "%s/%s", FilePath_Data_ptr, FileName_ptr);
	outfile.open(filepath);
	if (outfile.fail()) {
		printf("%c file could not be opened. Try correcting the file's location path: %c\n", FileName_ptr, FilePath_Data_ptr);
		//cout << " file could not be opened. Try correcting the file's location path." << endl;
		//cout << filepath << endl;
		system("pause");
		exit(1);
	}

	for (int i = 0; i < size; i++) {
		outfile << Variable[i] << std::endl;
	}
	outfile.close();

	return 0;
}
int ComputeDistanceMatrix() {
	for (i = 0; i < imax + 1; i++) {
		for (j = 0; j < jmax + 1; j++) {
			Distance_ij[i][j] = sqrt((XCOORD_i[i] - XCOORD_i[j]) * (XCOORD_i[i] - XCOORD_i[j]) + (YCOORD_i[i] - YCOORD_i[j]) * (YCOORD_i[i] - YCOORD_i[j]));
		}
	}
	/*for (i = 0; i < imax + 1; i++) {
		Distance_ij[i][i]= Big_M;
	}*/
	return 0;
}
int AllocateMemory() {
	int imax_plus = imax + 1;
	int jmax_plus = jmax + 1;

	EdgeCat_ij = new int* [imax_plus];
	Distance_ij = new double* [imax_plus];
	X_ijValue = new double* [imax_plus];
	for (i = 0; i < imax_plus; i++) {
		EdgeCat_ij[i] = new int[jmax_plus];
		Distance_ij[i] = new double[jmax_plus];
		X_ijValue[i] = new double[jmax_plus];
	}
	Speed_ijp = new double** [imax_plus];
	w_ijm = new double** [imax_plus];
	w_max_m = new double[mmax];
	w_min_m = new double[mmax];
	TravelTime_ijm = new double** [imax_plus];
	TravelTimeCalculated_ijm = new double** [imax_plus];
	TravelTimeAverage_ijm = new double** [imax_plus];
	TravelTimeMinimum_ijm = new double** [imax_plus];
	TravelTimeMinimum_ij = new double* [imax_plus];
	theta_ijm = new float** [imax_plus];
	zeta_ijm = new float** [imax_plus];
	for (i = 0; i < imax_plus; i++) {
		Speed_ijp[i] = new double* [jmax_plus];
		w_ijm[i] = new double* [jmax_plus];
		TravelTime_ijm[i] = new double* [jmax_plus];
		TravelTimeCalculated_ijm[i] = new double* [jmax_plus];
		TravelTimeAverage_ijm[i] = new double* [jmax_plus];
		TravelTimeMinimum_ijm[i] = new double* [jmax_plus];
		TravelTimeMinimum_ij[i] = new double[jmax_plus];
		theta_ijm[i] = new float* [jmax_plus];
		zeta_ijm[i] = new float* [jmax_plus];
	}
	for (i = 0; i < imax_plus; i++) {
		for (j = 0; j < jmax_plus; j++) {
			Speed_ijp[i][j] = new double[pmax];
			w_ijm[i][j] = new double[mmax];
			TravelTime_ijm[i][j] = new double[mmax];
			TravelTimeCalculated_ijm[i][j] = new double[mmax];
			TravelTimeAverage_ijm[i][j] = new double[mmax];
			TravelTimeMinimum_ijm[i][j] = new double[mmax];
			theta_ijm[i][j] = new float[mmax];
			zeta_ijm[i][j] = new float[mmax];
		}
	}

	DualValueCon12_ZZY_k = new double[kmax];
	DualValueCon13_ZZY_kr = new double* [kmax];
	DualValueCon14_ZZY_kr = new double* [kmax];
	for (k = 0; k < kmax; k++) {
		DualValueCon13_ZZY_kr[k] = new double[rmax];
		DualValueCon14_ZZY_kr[k] = new double[rmax];
	}
	X_ijkrmValue = new double**** [imax_plus];
	X_ijrmValue = new double*** [imax_plus];
	OptimalX_ijkrmValue = new double**** [imax_plus];
	DualValueCon9_ZZZX_ijkrm = new double**** [imax_plus];
	DualValueCon11a_ZX_ijkrm = new double**** [imax_plus];
	DualValueCon11b_ZX_ijkrm = new double**** [imax_plus];
	//Z_ijkrmValue = new double****[imax_plus];
	Y_ikrValue = new double** [imax_plus];
	Y_irValue = new double* [imax_plus];
	Y_iValue = new double[imax_plus];
	OptimalY_ikrValue = new double** [imax_plus];
	ZZ_ikrValue = new double** [imax_plus];
	OptimalZZ_ikrValue = new double** [imax_plus];
	DualValueCon10a_ZZY_ikr = new double** [imax_plus];
	DualValueCon10b_ZZY_ikr = new double** [imax_plus];
	for (i = 0; i < imax_plus; i++) {
		X_ijkrmValue[i] = new double*** [jmax_plus];
		X_ijrmValue[i] = new double** [jmax_plus];
		OptimalX_ijkrmValue[i] = new double*** [jmax_plus];
		DualValueCon9_ZZZX_ijkrm[i] = new double*** [jmax_plus];
		DualValueCon11a_ZX_ijkrm[i] = new double*** [jmax_plus];
		DualValueCon11b_ZX_ijkrm[i] = new double*** [jmax_plus];
		//Z_ijkrmValue[i] = new double***[jmax_plus];
		Y_ikrValue[i] = new double* [kmax];
		Y_irValue[i] = new double[rmax];
		OptimalY_ikrValue[i] = new double* [kmax];
		ZZ_ikrValue[i] = new double* [kmax];
		OptimalZZ_ikrValue[i] = new double* [kmax];
		DualValueCon10a_ZZY_ikr[i] = new double* [kmax];
		DualValueCon10b_ZZY_ikr[i] = new double* [kmax];
	}
	for (i = 0; i < imax_plus; i++) {
		for (j = 0; j < jmax_plus; j++) {
			X_ijkrmValue[i][j] = new double** [kmax];
			X_ijrmValue[i][j] = new double* [rmax];
			OptimalX_ijkrmValue[i][j] = new double** [kmax];
			DualValueCon9_ZZZX_ijkrm[i][j] = new double** [kmax];
			DualValueCon11a_ZX_ijkrm[i][j] = new double** [kmax];
			DualValueCon11b_ZX_ijkrm[i][j] = new double** [kmax];
			//Z_ijkrmValue[i][j] = new double**[kmax];
		}
		for (k = 0; k < kmax; k++) {
			Y_ikrValue[i][k] = new double[rmax];
			OptimalY_ikrValue[i][k] = new double[rmax];
			ZZ_ikrValue[i][k] = new double[rmax];
			OptimalZZ_ikrValue[i][k] = new double[rmax];
			DualValueCon10a_ZZY_ikr[i][k] = new double[rmax];
			DualValueCon10b_ZZY_ikr[i][k] = new double[rmax];
		}
	}

	for (i = 0; i < imax_plus; i++) {
		for (j = 0; j < jmax_plus; j++) {
			for (k = 0; k < kmax; k++) {
				X_ijkrmValue[i][j][k] = new double* [rmax];
				OptimalX_ijkrmValue[i][j][k] = new double* [rmax];
				DualValueCon9_ZZZX_ijkrm[i][j][k] = new double* [rmax];
				DualValueCon11a_ZX_ijkrm[i][j][k] = new double* [rmax];
				DualValueCon11b_ZX_ijkrm[i][j][k] = new double* [rmax];
				//Z_ijkrmValue[i][j][k] = new double*[rmax];
			}
		}
	}
	for (i = 0; i < imax_plus; i++) {
		for (j = 0; j < jmax_plus; j++) {
			for (r = 0; r < rmax; r++) {
				X_ijrmValue[i][j][r] = new double[mmax];
			}
		}
	}
	for (i = 0; i < imax_plus; i++) {
		for (j = 0; j < jmax_plus; j++) {
			for (k = 0; k < kmax; k++) {
				for (r = 0; r < rmax; r++) {
					X_ijkrmValue[i][j][k][r] = new double[mmax];
					OptimalX_ijkrmValue[i][j][k][r] = new double[mmax];
					DualValueCon9_ZZZX_ijkrm[i][j][k][r] = new double[mmax];
					DualValueCon11a_ZX_ijkrm[i][j][k][r] = new double[mmax];
					DualValueCon11b_ZX_ijkrm[i][j][k][r] = new double[mmax];
					//Z_ijkrmValue[i][j][k][r] = new double[mmax];
				}
			}
		}
	}
	SpeedBreakPoint_p = new double[pmax];
	return 0;
}
int ComputeBreakpoints() {
	//Compute the time at which the speed changes from one period to the next one

	DayDuration = l_i[0];//The maximum arrival time at the ending depot
	cout << "DayDuration=" << DayDuration << endl;
	for (p = 0; p < pmax; p++) {
		SpeedBreakPoint_p[p] = BPoint_p[p] * DayDuration;
		if (p > 0) {
			SpeedBreakPoint_p[p] = SpeedBreakPoint_p[p] + SpeedBreakPoint_p[p - 1];
		}
		//cout << "SpeedBreakPoint_p[" << p << "]=" << SpeedBreakPoint_p[p] << endl;
	}

	//HOW TO COMPUTE w_ijm???????
	for (i = 0; i < imax + 1; i++) {
		for (j = 0; j < jmax + 1; j++) {
			int ArcCategory = EdgeCat_ij[i][j];
			for (p = 0; p < pmax; p++) {
				Speed_ijp[i][j][p] = SpeedOfCatOverTime_p_c[p][ArcCategory];
			}
		}
	}
	if (FileName_Problem[1] != 'c' && FileName_Problem[0] == 'r') {
		for (i = 0; i < imax + 1; i++) {
			for (j = 0; j < jmax + 1; j++) {
				for (p = 0; p < pmax; p++) {
					Speed_ijp[i][j][p] = Speed_ijp[i][j][p] * 2;
				}
			}
		}
	}
	for (i = 0; i < imax + 1; i++) {
		for (j = 0; j < jmax + 1; j++) {
			m = 1;
			p = 0;
			while (m < mmax) {
				w_ijm[i][j][m] = SpeedBreakPoint_p[p];
				m = m + 2;
				p++;
			}

		}
	}
	/*for (m = 0; m < mmax; m++) {
		cout << "w_ijm[" << m << "]=" << w_ijm[0][1][m] << endl;
	}*/

	for (i = 0; i < imax + 1; i++) {
		for (j = 0; j < jmax + 1; j++) {
			m = 0;
			p = 0;
			while (m < mmax) {
				w_ijm[i][j][m] = SpeedBreakPoint_p[p] - (Distance_ij[i][j] / Speed_ijp[i][j][p]);
				m = m + 2;
				p++;
			}

		}
	}
	for (m = 0; m < mmax; m++) {
		w_max_m[m] = 0;
		w_min_m[m] = Big_M;
		for (i = 0; i < imax + 1; i++) {
			for (j = 0; j < jmax + 1; j++) {
				w_max_m[m] = max(w_max_m[m], w_ijm[i][j][m]);
				if (w_ijm[i][j][m] > 0) w_min_m[m] = min(w_min_m[m], w_ijm[i][j][m]);
			}
		}

	}
	/*for (m = 0; m < mmax; m++) {
		cout << w_ijm[0][1][m] << endl;
	}*/
	//Compute travel time in m-th time interval
	p = 0;
	for (i = 0; i < imax + 1; i++) {
		for (j = 0; j < jmax + 1; j++) {
			for (m = 0; m < mmax; m++) {
				p = floor(m / 2);
				TravelTime_ijm[i][j][m] = Distance_ij[i][j] / Speed_ijp[i][j][p];
			}
		}
	}
	//Compute slope theta(i,j,m)
	//Compute intersection with y-axis zeta(i,j,m)

	for (i = 0; i < imax + 1; i++) {
		for (j = 0; j < jmax + 1; j++) {
			theta_ijm[i][j][0] = 0;
			zeta_ijm[i][j][0] = TravelTime_ijm[i][j][0];
			for (m = 1; m < mmax; m++) {
				if (i == j) {
					theta_ijm[i][j][m] = 0;
					zeta_ijm[i][j][m] = TravelTime_ijm[i][j][0];
				}
				else {
					theta_ijm[i][j][m] = (TravelTime_ijm[i][j][m] - TravelTime_ijm[i][j][m - 1]) / (w_ijm[i][j][m] - w_ijm[i][j][m - 1]);
					zeta_ijm[i][j][m] = (w_ijm[i][j][m] * TravelTime_ijm[i][j][m - 1] - w_ijm[i][j][m - 1] * TravelTime_ijm[i][j][m]) / (w_ijm[i][j][m] - w_ijm[i][j][m - 1]);
				}
				theta_ijm[0][imax][m] = 0;
				zeta_ijm[0][imax][m] = TravelTime_ijm[0][imax][0];
				theta_ijm[imax][0][m] = 0;
				zeta_ijm[imax][0][m] = TravelTime_ijm[imax][0][0];
			}
		}
	}

	for (i = 0; i < imax + 1; i++) {
		for (j = 0; j < jmax + 1; j++) {
			TravelTimeMinimum_ij[i][j] = Big_M;
			for (m = 0; m < mmax; m++) {
				TravelTimeCalculated_ijm[i][j][m] = theta_ijm[i][j][m] * w_ijm[i][j][m] + zeta_ijm[i][j][m];
				if (m > 0) {
					TravelTimeAverage_ijm[i][j][m] = abs(TravelTimeCalculated_ijm[i][j][m] + TravelTimeCalculated_ijm[i][j][m - 1]) / 2;
					TravelTimeMinimum_ijm[i][j][m] = min(TravelTimeCalculated_ijm[i][j][m - 1], TravelTimeCalculated_ijm[i][j][m]);
				}
				else {
					TravelTimeAverage_ijm[i][j][m] = TravelTimeCalculated_ijm[i][j][m];
					TravelTimeMinimum_ijm[i][j][m] = TravelTimeCalculated_ijm[i][j][m];
				}
				if (TravelTimeMinimum_ij[i][j] > TravelTimeMinimum_ijm[i][j][m]) TravelTimeMinimum_ij[i][j] = TravelTimeMinimum_ijm[i][j][m];
			}
		}
	}

	return 0;
}
int load_data(char* FilePath_Data_ptr) {
	int status;
	char* FileName_ptr;
	char* FileName_ptr2;
	string read_file = "";
	//-------------------Declare Data of the problem--------------------
	//Initializing

	//for (i = 0; i < imax; i++) {
	//	WWP_i[i] = 0;
	//	for (j = 0; j < jmax; j++) {
	//		CP_ij[i][j] = 0;
	//		CPM_ij[i][j] = 0;
	//		OptimalCP_ij[i][j] = 0;
	//		OptimalCPM_ij[i][j] = 0;
	//	}
	//}

	FileName_ptr2 = FileName_Problem;

	//Read all data
	FileName_ptr = "time_dep.dat";
	status = ReadTimeDepFile(FilePath_Data_ptr, FileName_ptr, FileName_ptr2);
	if (status != 0) {
		Found_Error("ReadTimeDepFile");
		return -1;
	}
	mmax = 2 * pmax;//the travel time periods are twice the speed periods
	//FileName_ptr = "instructions.txt";
	/*status = ReadInstructionsFile(FilePath_Data_ptr, FileName_ptr);
	if (status != 0) {
		Found_Error("ReadFileDouble");
		return -1;
	}*/

	status = ReadCustomersFile(FilePath_Data_ptr, FileName_ptr2);
	if (status != 0) {
		Found_Error("ReadCustomersFile");
		return -1;
	}
	status = AllocateMemory();
	if (status != 0) {
		Found_Error("AllocateMemory");
		return -1;
	}
	FileName_ptr = "edge_cat.dat";
	status = ReadFileDouble(FilePath_Data_ptr, FileName_ptr, imax, imax, EdgeCat_ij);
	if (status != 0) {
		Found_Error("ReadFileDouble");
		return -1;
	}
	//Node n+1 is the same as node 0
	for (int i = 0; i < imax; i++) {
		EdgeCat_ij[imax][i] = EdgeCat_ij[0][i];
		EdgeCat_ij[i][imax] = EdgeCat_ij[i][0];
	}
	EdgeCat_ij[imax][imax] = EdgeCat_ij[0][0];
	status = ComputeDistanceMatrix();
	if (status != 0) {
		Found_Error("ComputeDistanceMatrix");
		return -1;
	}
	status = ComputeBreakpoints();
	if (status != 0) {
		Found_Error("ComputeBreakpoints");
		return -1;
	}

	// End of DATA///////////////////////////
	return 0;
}
int do_master(IloEnv env, IloModel modelMaster, IloNumVarMatrix5x5 X_ijkrm, IloNumVarMatrix3x3 Y_ikr, IloNumVarMatrix3x3 U_ikr, IloNumVarArray Heta_k, IloRangeMatrix2x2 Con2_YX_kr, IloRangeMatrix2x2 Con3_YX_kr, IloRangeMatrix3x3 Con4a_YX_ikr, IloRangeMatrix3x3 Con4b_YX_ikr, IloRangeArray Con5_Y_i, IloRangeMatrix2x2 Con6_Y_kr, IloRangeMatrix4x4 Con15_XX_ikrm, IloRangeMatrix5x5 Con16_X_ijkrm, IloRangeMatrix3x3 Con17_XX_krm, IloRangeMatrix2x2 Con18_Y_kr, IloRangeMatrix2x2 Con19_Y_kr, IloRangeMatrix2x2 Con20_X_kr, IloRangeMatrix3x3 Con20a_XX_krm, IloRangeMatrix3x3 Con21_XX_ikr, IloRangeMatrix3x3 Con22_X_ijm, IloRangeMatrix3x3 Con23_Xw_krm, IloRangeArray Con24_hX_n, IloRangeArray Con24a_hX_m, IloRangeArray Con25_hX_n, IloRangeMatrix4x4 Con26_YY_ijkr, IloRangeArray Con27_hX_n, IloRangeMatrix2x2 Con28_Y_kr, IloRangeMatrix4x4 Con29_XX_ijkr, IloRangeMatrix5x5 Con30_XXX_ijlkr, IloRangeMatrix4x4 Con31_XX_ijlm, IloRangeMatrix2x2 Con32_XY_kr, IloRangeArray ConAuxiliary_i, IloRangeMatrix4x4 ConSEC_ijkr, IloRangeArray ConAuxiliary2_n) {

	char CharMasterVar[60];
	char CharMasterCon[60];
	double LBMasterCon = 0;
	double UBMasterCon = 0;
	NoOfMasterVars = 0;
	NoOfMasterCons = 0;
	//------------------------------------------------------------------------------
	//---------------------------------- MASTER ------------------------------------
	//------------------------------------------------------------------------------
	//----------------------------- Master Variable --------------------------------
	//-------------- Decision Variable X_ijkrm ---------------------------------------
	for (i = 0; i < imax + 1; i++) {
		IloNumVarMatrix4x4 X_jkrm(env, 0);
		for (j = 0; j < jmax + 1; j++) {
			IloNumVarMatrix3x3 X_krm(env, 0);
			for (k = 0; k < kmax; k++) {
				IloNumVarMatrix2x2 X_rm(env, 0);
				for (r = 0; r < rmax; r++) {
					IloNumVarArray X_m(env, 0);
					for (m = 0; m < mmax; m++) {
						sprintf(CharMasterVar, "X_ijkrm(i%d,j%d,k%d,r%d,m%d)", i, j, k, r, m);
						IloNumVar X(env, 0, 1, ILOINT, CharMasterVar);
						NoOfMasterVars++;
						X_m.add(X);
					}
					X_rm.add(X_m);
				}
				X_krm.add(X_rm);
			}
			X_jkrm.add(X_krm);
		}
		X_ijkrm.add(X_jkrm);
	}
	//-------------- Decision Variable Y_ikr ---------------------------------------
	for (i = 0; i < imax + 1; i++) {
		IloNumVarMatrix2x2 Y_kr(env, 0);
		for (k = 0; k < kmax; k++) {
			IloNumVarArray Y_r(env, 0);
			for (r = 0; r < rmax; r++) {
				sprintf(CharMasterVar, "Y_ikr(i%d,k%d,r%d)", i, k, r);
				IloNumVar Y(env, 0, 1, ILOINT, CharMasterVar);
				NoOfMasterVars++;
				Y_r.add(Y);
			}
			Y_kr.add(Y_r);
		}
		Y_ikr.add(Y_kr);
	}

	//-------------- Decision Variable U_ikr ---------------------------------------
	for (i = 0; i < imax + 1; i++) {
		IloNumVarMatrix2x2 U_kr(env, 0);
		for (k = 0; k < kmax; k++) {
			IloNumVarArray U_r(env, 0);
			for (r = 0; r < rmax; r++) {
				sprintf(CharMasterVar, "U_ikr(i%d,k%d,r%d)", i, k, r);
				IloNumVar U(env, 0, imax + 1, ILOINT, CharMasterVar);
				NoOfMasterVars++;
				U_r.add(U);
			}
			U_kr.add(U_r);
		}
		U_ikr.add(U_kr);
	}

	//-------------- Decision Variable Heta_k ---------------------------------------
	for (k = 0; k < kmax; k++) {
		sprintf(CharMasterVar, "Heta_k(k%d)", k);
		IloNumVar Heta(env, 0, Big_M, ILOFLOAT, CharMasterVar);
		NoOfMasterVars++;
		Heta_k.add(Heta);
	}


	//-----------------------------Finish of Master Variables --------------------------------

	//-----------------------------------------------------------------------------
	//-------------------------Start of Master Constraints-----------------------------------------
	//------------------------------------------------------------------------------
	//------------------------------------------------------------------------------




	//-------------------------- Constraint Con2_YX_kr2 -------------------------
	for (k = 0; k < kmax; k++) {
		IloRangeArray Con2_YX_r(env, 0);
		for (r = 0; r < rmax; r++) {
			IloExpr expr(env, 0);
			for (j = 1; j < jmax; j++) {
				for (m = 0; m < mmax; m++) {
					expr -= X_ijkrm[0][j][k][r][m];
				}
			}
			expr += Y_ikr[0][k][r];
			sprintf(CharMasterCon, "Con2_YX_kr(k%d,r%d)", k, r);
			LBMasterCon = 0, UBMasterCon = 0;
			IloRange Con2_YX(env, LBMasterCon, expr, UBMasterCon, CharMasterCon);
			NoOfMasterCons++;
			modelMaster.add(Con2_YX);
			Con2_YX_r.add(Con2_YX);
			expr.end();
		}
		Con2_YX_kr.add(Con2_YX_r);
	}

	//-------------------------- Constraint Con3_YX_kr -------------------------
	for (k = 0; k < kmax; k++) {
		IloRangeArray Con3_YX_r(env, 0);
		for (r = 0; r < rmax; r++) {
			IloExpr expr(env, 0);
			for (j = 1; j < jmax; j++) {
				for (m = 0; m < mmax; m++) {
					expr -= X_ijkrm[j][imax][k][r][m];
				}
			}
			expr += Y_ikr[imax][k][r];
			sprintf(CharMasterCon, "Con3_YX_kr(k%d,r%d)", k, r);
			LBMasterCon = 0, UBMasterCon = 0;
			IloRange Con3_YX(env, LBMasterCon, expr, UBMasterCon, CharMasterCon);
			NoOfMasterCons++;
			modelMaster.add(Con3_YX);
			Con3_YX_r.add(Con3_YX);
			expr.end();
		}
		Con3_YX_kr.add(Con3_YX_r);
	}


	//-------------------------- Constraint Con4a_YX_ikr -------------------------
	for (i = 1; i < imax; i++) {
		IloRangeMatrix2x2 Con4a_YX_kr(env, 0);
		for (k = 0; k < kmax; k++) {
			IloRangeArray Con4a_YX_r(env, 0);
			for (r = 0; r < rmax; r++) {
				IloExpr expr(env, 0);
				for (j = 0; j < jmax; j++) {
					if (j != i) {
						for (m = 0; m < mmax; m++) {
							expr -= X_ijkrm[j][i][k][r][m];
						}
					}
				}
				expr += Y_ikr[i][k][r];
				sprintf(CharMasterCon, "Con4a_YX_ikr(i%d,k%d,r%d)", i, k, r);
				LBMasterCon = 0, UBMasterCon = 0;
				IloRange Con4a_YX(env, LBMasterCon, expr, UBMasterCon, CharMasterCon);
				NoOfMasterCons++;
				modelMaster.add(Con4a_YX);
				Con4a_YX_r.add(Con4a_YX);
				expr.end();
			}
			Con4a_YX_kr.add(Con4a_YX_r);
		}
		Con4a_YX_ikr.add(Con4a_YX_kr);
	}

	//-------------------------- Constraint Con4b_YX_ikr -------------------------
	for (i = 1; i < imax; i++) {
		IloRangeMatrix2x2 Con4b_YX_kr(env, 0);
		for (k = 0; k < kmax; k++) {
			IloRangeArray Con4b_YX_r(env, 0);
			for (r = 0; r < rmax; r++) {
				IloExpr expr(env, 0);
				/*for (j = 0; j < jmax; j++) {
					if (j != i) {
						for (m = 0; m < mmax; m++) {
							expr += X_ijkrm[j][i][k][r][m];
						}
					}
				}*/
				expr += Y_ikr[i][k][r];
				for (j = 1; j < jmax + 1; j++) {
					if (j != i) {
						for (m = 0; m < mmax; m++) {
							expr -= X_ijkrm[i][j][k][r][m];
						}
					}
				}
				sprintf(CharMasterCon, "Con4b_YX_ikr(i%d,k%d,r%d)", i, k, r);
				LBMasterCon = 0, UBMasterCon = 0;
				IloRange Con4b_YX(env, LBMasterCon, expr, UBMasterCon, CharMasterCon);
				NoOfMasterCons++;
				modelMaster.add(Con4b_YX);
				Con4b_YX_r.add(Con4b_YX);
				expr.end();
			}
			Con4b_YX_kr.add(Con4b_YX_r);
		}
		Con4b_YX_ikr.add(Con4b_YX_kr);
	}

	//-------------------------- Constraint Con5_Y_i -------------------------
	for (i = 1; i < imax; i++) {
		IloExpr expr(env, 0);
		for (k = 0; k < kmax; k++) {
			for (r = 0; r < rmax; r++) {
				expr += Y_ikr[i][k][r];
			}
		}
		sprintf(CharMasterCon, "Con5_Y_i(i%d)", i);
		LBMasterCon = 1, UBMasterCon = 1;
		IloRange Con5_Y(env, LBMasterCon, expr, UBMasterCon, CharMasterCon);
		NoOfMasterCons++;
		modelMaster.add(Con5_Y);
		Con5_Y_i.add(Con5_Y);
		expr.end();
	}

	//-------------------------- Constraint Con6_Y_kr -------------------------
	for (k = 0; k < kmax; k++) {
		IloRangeArray Con6_Y_r(env, 0);
		for (r = 0; r < rmax; r++) {
			IloExpr expr(env, 0);
			for (i = 1; i < imax; i++) {
				expr += q_i[i] * Y_ikr[i][k][r];
			}
			sprintf(CharMasterCon, "Con6_Y_kr(k%d,r%d)", k, r);
			LBMasterCon = -IloInfinity, UBMasterCon = Q;
			IloRange Con6_Y(env, LBMasterCon, expr, UBMasterCon, CharMasterCon);
			NoOfMasterCons++;
			modelMaster.add(Con6_Y);
			Con6_Y_r.add(Con6_Y);
			expr.end();
		}
		Con6_Y_kr.add(Con6_Y_r);
	}
	//-------------------------- Constraint Con15_XX_ikrm -------------------------
	for (i = 1; i < imax; i++) {
		IloRangeMatrix3x3 Con15_XX_krm(env, 0);
		for (k = 0; k < kmax; k++) {
			IloRangeMatrix2x2 Con15_XX_rm(env, 0);
			for (r = 0; r < rmax; r++) {
				IloRangeArray Con15_XX_m(env, 0);
				for (m = 0; m < mmax; m++) {
					IloExpr expr(env, 0);
					for (j = 1; j < jmax + 1; j++) {
						if (j != i) {
							for (p = m; p < mmax; p++) {
								expr += X_ijkrm[i][j][k][r][p];
							}
						}
					}
					for (j = 0; j < jmax; j++) {
						if (j != i) {
							expr -= X_ijkrm[j][i][k][r][m];
						}
					}
					sprintf(CharMasterCon, "Con15_XX_ikrm(i%d,k%d,r%d,m%d)", i, k, r, m);
					LBMasterCon = 0, UBMasterCon = IloInfinity;
					IloRange Con15_XX(env, LBMasterCon, expr, UBMasterCon, CharMasterCon);
					NoOfMasterCons++;
					modelMaster.add(Con15_XX);
					Con15_XX_m.add(Con15_XX);
					expr.end();
				}
				Con15_XX_rm.add(Con15_XX_m);
			}
			Con15_XX_krm.add(Con15_XX_rm);
		}
		Con15_XX_ikrm.add(Con15_XX_krm);
	}

	//-------------------------- Constraint Con16_X_ijkrm -------------------------
	for (i = 1; i < imax; i++) {
		IloRangeMatrix4x4 Con16_X_jkrm(env, 0);
		for (j = 1; j < jmax + 1; j++) {
			if (i != j) {
				IloRangeMatrix3x3 Con16_X_krm(env, 0);
				for (k = 0; k < kmax; k++) {
					IloRangeMatrix2x2 Con16_X_rm(env, 0);
					for (r = 0; r < rmax; r++) {
						IloRangeArray Con16_X_m(env, 0);
						for (m = 0; m < mmax; m++) {
							if (m > 0) {
								if (w_ijm[i][j][m - 1] > l_i[i] + s_i[i] || w_ijm[i][j][m] < e_i[i] + s_i[i]) {//
									IloExpr expr(env, 0);
									expr = X_ijkrm[i][j][k][r][m];
									sprintf(CharMasterCon, "Con16_X_ijkrm(i%d,j%d,k%d,r%d,m%d)", i, j, k, r, m);
									LBMasterCon = -IloInfinity, UBMasterCon = 0;
									IloRange Con16_X(env, LBMasterCon, expr, UBMasterCon, CharMasterCon);
									NoOfMasterCons++;
									modelMaster.add(Con16_X);
									Con16_X_m.add(Con16_X);
									expr.end();
								}
							}
							else {
								if (w_ijm[i][j][m] < e_i[i] + s_i[i]) {//
									IloExpr expr(env, 0);
									expr = X_ijkrm[i][j][k][r][m];
									sprintf(CharMasterCon, "Con16_X_ijkrm(i%d,j%d,k%d,r%d,m%d)", i, j, k, r, m);
									LBMasterCon = -IloInfinity, UBMasterCon = 0;
									IloRange Con16_X(env, LBMasterCon, expr, UBMasterCon, CharMasterCon);
									NoOfMasterCons++;
									modelMaster.add(Con16_X);
									Con16_X_m.add(Con16_X);
									expr.end();
								}
							}
						}
						Con16_X_rm.add(Con16_X_m);
					}
					Con16_X_krm.add(Con16_X_rm);
				}
				Con16_X_jkrm.add(Con16_X_krm);
			}
		}
		Con16_X_ijkrm.add(Con16_X_jkrm);
	}

	//-------------------------- Constraint Con17_XX_krm -------------------------
	for (k = 0; k < kmax; k++) {
		IloRangeMatrix2x2 Con17_XX_rm(env, 0);
		for (r = 1; r < rmax; r++) {
			IloRangeArray Con17_XX_m(env, 0);
			for (m = 0; m < mmax; m++) {
				IloExpr expr(env, 0);
				for (j = 1; j < jmax + 1; j++) {
					for (p = m; p < mmax; p++) {
						expr += X_ijkrm[0][j][k][r][p];
					}
				}
				for (j = 0; j < jmax; j++) {
					expr -= X_ijkrm[j][imax][k][r - 1][m];
				}
				sprintf(CharMasterCon, "Con17_XX_krm(k%d,r%d,m%d)", k, r, m);
				LBMasterCon = 0, UBMasterCon = IloInfinity;
				IloRange Con17_XX(env, LBMasterCon, expr, UBMasterCon, CharMasterCon);
				NoOfMasterCons++;
				modelMaster.add(Con17_XX);
				Con17_XX_m.add(Con17_XX);
				expr.end();
			}
			Con17_XX_rm.add(Con17_XX_m);
		}
		Con17_XX_krm.add(Con17_XX_rm);
	}

	//-------------------------- Constraint Con20_X_kr -------------------------
	for (k = 0; k < kmax; k++) {
		IloRangeArray Con20_X_r(env, 0);
		for (r = 0; r < rmax; r++) {
			IloExpr expr(env, 0);
			for (m = 0; m < mmax; m++) {
				for (j = 1; j < jmax + 1; j++) {
					expr -= w_ijm[0][j][m] * X_ijkrm[0][j][k][r][m];
				}
				if (m > 0) {
					for (j = 0; j < jmax; j++) {
						expr += w_ijm[j][imax][m - 1] * X_ijkrm[j][imax][k][r][m];
					}
				}
			}
			for (j = 1; j < jmax; j++) {
				expr += lamda * s_i[j] * Y_ikr[j][k][r];
			}
			sprintf(CharMasterCon, "Con20_X_kr(k%d,r%d)", k, r);
			LBMasterCon = -IloInfinity, UBMasterCon = MaxTripDuration;
			IloRange Con20_X(env, LBMasterCon, expr, UBMasterCon, CharMasterCon);
			NoOfMasterCons++;
			modelMaster.add(Con20_X);
			Con20_X_r.add(Con20_X);
			expr.end();
		}
		Con20_X_kr.add(Con20_X_r);
	}

	//-------------------------- Constraint Con20a_XX_krm -------------------------
	for (k = 0; k < kmax; k++) {
		IloRangeMatrix2x2 Con20a_XX_rm(env, 0);
		for (r = 0; r < rmax; r++) {
			IloRangeArray Con20a_XX_m(env, 0);
			for (m = 1; m < mmax; m++) {
				IloExpr expr(env, 0);
				for (i = 0; i < imax; i++) {
					expr += X_ijkrm[i][jmax][k][r][m] * (w_ijm[i][jmax][m - 1]);
					for (j = 0; j < jmax + 1; j++) {
						expr += X_ijkrm[i][j][k][r][m] * (TravelTimeMinimum_ijm[i][j][m] + s_i[j]);
					}
				}
				for (p = 0; p < mmax; p++) {
					for (j = 0; j < jmax + 1; j++) {
						expr -= X_ijkrm[0][j][k][r][p] * (w_ijm[0][j][p]);
					}
				}
				/*for (j = 1; j < jmax; j++) {
					expr += lamda * s_i[j] * Y_ikr[j][k][r];
				}*/
				sprintf(CharMasterCon, "Con20a_XX_krm(k%d,r%d,m%d)", k, r, m);
				LBMasterCon = -IloInfinity, UBMasterCon = MaxTripDuration;
				IloRange Con20a_XX(env, LBMasterCon, expr, UBMasterCon, CharMasterCon);
				NoOfMasterCons++;
				modelMaster.add(Con20a_XX);
				Con20a_XX_m.add(Con20a_XX);
				expr.end();
			}
			Con20a_XX_rm.add(Con20a_XX_m);
		}
		Con20a_XX_krm.add(Con20a_XX_rm);
	}

	//-------------------------- Constraint Con21_XX_ikr -------------------------
	for (i = 1; i < imax; i++) {
		IloRangeMatrix2x2 Con21_XX_kr(env, 0);
		for (k = 0; k < kmax; k++) {
			IloRangeArray Con21_XX_r(env, 0);
			for (r = 0; r < rmax; r++) {
				IloExpr expr(env, 0);
				for (m = 0; m < mmax; m++) {
					for (j = 1; j < jmax + 1; j++) {
						expr += w_ijm[i][j][m] * X_ijkrm[i][j][k][r][m];
					}
					for (j = 0; j < jmax; j++) {
						if (m > 0) {
							expr -= (w_ijm[j][i][m - 1] + TravelTimeMinimum_ijm[j][i][m]) * X_ijkrm[j][i][k][r][m];
						}
						else {
							expr -= (TravelTimeMinimum_ijm[j][i][m]) * X_ijkrm[j][i][k][r][m];
						}
					}
				}
				//expr -= s_i[i];
				sprintf(CharMasterCon, "Con21_XX_ikr(i%d,k%d,r%d)", i, k, r);
				LBMasterCon = 0, UBMasterCon = IloInfinity;
				IloRange Con21_XX(env, LBMasterCon, expr, UBMasterCon, CharMasterCon);
				NoOfMasterCons++;
				modelMaster.add(Con21_XX);
				Con21_XX_r.add(Con21_XX);
				expr.end();
			}
			Con21_XX_kr.add(Con21_XX_r);
		}
		Con21_XX_ikr.add(Con21_XX_kr);
	}

	//-------------------------- Constraint Con22_X_ijm -------------------------
	for (i = 0; i < imax; i++) {
		IloRangeMatrix2x2 Con22_X_jm(env, 0);
		for (j = 1; j < jmax + 1; j++) {
			IloRangeArray Con22_X_m(env, 0);
			for (m = 0; m < mmax; m++) {
				if (m > 0) {
					if (l_i[j] < e_i[i] + TravelTimeMinimum_ijm[i][j][m] + s_i[i]) {//|| l_i[j] < w_ijm[i][j][m - 1] + TravelTimeMinimum_ijm[i][j][m] + s_i[i]) {
						IloExpr expr(env, 0);
						for (k = 0; k < kmax; k++) {
							for (r = 0; r < rmax; r++) {
								expr += X_ijkrm[i][j][k][r][m];
							}
						}
						//expr -= s_i[i];
						sprintf(CharMasterCon, "Con22_X_ijm(i%d,j%d,m%d)", i, j, m);
						LBMasterCon = -IloInfinity, UBMasterCon = 0;
						IloRange Con22_X(env, LBMasterCon, expr, UBMasterCon, CharMasterCon);
						NoOfMasterCons++;
						modelMaster.add(Con22_X);
						Con22_X_m.add(Con22_X);
						expr.end();
					}
				}
				else {
					if (l_i[j] < e_i[i] + TravelTimeMinimum_ijm[i][j][m] + s_i[i]) {
						IloExpr expr(env, 0);
						for (k = 0; k < kmax; k++) {
							for (r = 0; r < rmax; r++) {
								expr += X_ijkrm[i][j][k][r][m];
							}
						}
						//expr -= s_i[i];
						sprintf(CharMasterCon, "Con22_X_ijm(i%d,j%d,m%d)", i, j, m);
						LBMasterCon = -IloInfinity, UBMasterCon = 0;
						IloRange Con22_X(env, LBMasterCon, expr, UBMasterCon, CharMasterCon);
						NoOfMasterCons++;
						modelMaster.add(Con22_X);
						Con22_X_m.add(Con22_X);
						expr.end();
					}

				}
			}
			Con22_X_jm.add(Con22_X_m);
		}
		Con22_X_ijm.add(Con22_X_jm);
	}

	//-------------------------- Constraint Con23_Xw_krm -------------------------
	for (k = 0; k < kmax; k++) {
		IloRangeMatrix2x2 Con23_Xw_rm(env, 0);
		for (r = 0; r < rmax; r++) {
			IloRangeArray Con23_Xw_m(env, 0);
			for (m = 0; m < mmax; m++) {
				IloExpr expr(env, 0);
				if (m > 0) {
					for (i = 0; i < imax; i++) {
						for (j = 1; j < jmax + 1; j++) {
							expr += X_ijkrm[i][j][k][r][m] * (TravelTimeMinimum_ijm[i][j][m] + s_i[i]);
						}
					}
					expr += -(w_max_m[m] - w_min_m[m - 1]);
				}
				else {
					for (i = 0; i < imax; i++) {
						for (j = 1; j < jmax + 1; j++) {
							expr += X_ijkrm[i][j][k][r][m] * (TravelTimeMinimum_ijm[i][j][m] + s_i[i]);
						}
					}
					expr += -(w_max_m[m]);
				}
				sprintf(CharMasterCon, "Con23_Xw_krm(k%d,r%d,m%d)", k, r, m);
				LBMasterCon = -IloInfinity, UBMasterCon = 0;
				IloRange Con23_Xw(env, LBMasterCon, expr, UBMasterCon, CharMasterCon);
				NoOfMasterCons++;
				modelMaster.add(Con23_Xw);
				Con23_Xw_m.add(Con23_Xw);
				expr.end();
			}
			Con23_Xw_rm.add(Con23_Xw_m);
		}
		Con23_Xw_krm.add(Con23_Xw_rm);
	}

	//-------------------------- Constraint Con24_hX_n -------------------------
	/*for (n = 0; n < 1; n++) {
		IloExpr expr(env, 0);
		for (k = 0; k < kmax; k++) {
			expr += Heta_k[k];
		}
		for (i = 0; i < imax; i++) {
			for (k = 0; k < kmax; k++) {
				for (r = 0; r < rmax; r++) {
					for (m = 0; m < mmax; m++) {
						if (m > 0) {
							expr -= g * X_ijkrm[i][jmax][k][r][m] * (TravelTimeMinimum_ijm[i][jmax][m] + w_ijm[i][jmax][m - 1]);
						}
						else {
							expr -= g * X_ijkrm[i][jmax][k][r][m] * (TravelTimeMinimum_ijm[i][jmax][m]);
						}
					}
				}
			}
		}
		sprintf(CharMasterCon, "Con24_hX_n(n%d)", n);
		LBMasterCon = 0, UBMasterCon = IloInfinity;
		IloRange Con24_hX(env, LBMasterCon, expr, UBMasterCon, CharMasterCon);
		NoOfMasterCons++;
		modelMaster.add(Con24_hX);
		Con24_hX_n.add(Con24_hX);
		expr.end();
	}*/

	//-------------------------- Constraint Con24a_hX_m -------------------------
	/*for (m = 0; m < mmax; m++) {
		IloExpr expr(env, 0);
		for (k = 0; k < kmax; k++) {
			for (r = 0; r < rmax; r++) {
				for (i = 0; i < imax; i++) {
					if (m > 0) {
						expr -= g * X_ijkrm[i][jmax][k][r][m] * (w_ijm[i][jmax][m - 1]);
					}
					for (j = 0; j < jmax + 1; j++) {
						expr -= g * X_ijkrm[i][j][k][r][m] * (TravelTimeMinimum_ijm[i][j][m] + s_i[j]);
					}
				}
			}
			expr += Heta_k[k];
		}
		sprintf(CharMasterCon, "Con24a_hX_m(m%d)", m);
		LBMasterCon = 0, UBMasterCon = IloInfinity;
		IloRange Con24a_hX(env, LBMasterCon, expr, UBMasterCon, CharMasterCon);
		NoOfMasterCons++;
		modelMaster.add(Con24a_hX);
		Con24a_hX_m.add(Con24a_hX);
		expr.end();
	}*/

	//-------------------------- Constraint Con25_hX_n -------------------------
	//for (n = 0; n < 1; n++) {
	//	IloExpr expr(env, 0);
	//	for (k = 0; k < kmax; k++) {
	//		for (i = 0; i < imax; i++) {
	//			for (r = 0; r < rmax; r++) {
	//				for (m = 0; m < mmax; m++) {
	//					//if (m > 0) {
	//						//if (w_ijm[i][jmax][m - 1] <= (e_i[i] + s_i[i]) && w_ijm[i][jmax][m] > (e_i[i] + s_i[i])) {//  if (w_ijm[i][j][m - 1] > l_i[i] + s_i[i] || w_ijm[i][j][m] < e_i[i] + s_i[i]) {//
	//					expr -= g * X_ijkrm[i][jmax][k][r][m] * (TravelTimeMinimum_ijm[i][jmax][m] + e_i[i] + s_i[i]);//
	//				//}
	//			//}
	//			//else {
	//				//if (w_ijm[i][jmax][m] > (e_i[i] + s_i[i])) {//
	//					//expr -= g * X_ijkrm[i][jmax][k][r][m] * (TravelTimeMinimum_ijm[i][jmax][m] + e_i[i] + s_i[i]);//
	//				//}
	//			//}
	//				}
	//			}
	//		}
	//		expr += Heta_k[k];
	//	}
	//	sprintf(CharMasterCon, "Con25_hX_n(n%d)", n);
	//	LBMasterCon = 0, UBMasterCon = IloInfinity;
	//	IloRange Con25_hX(env, LBMasterCon, expr, UBMasterCon, CharMasterCon);
	//	NoOfMasterCons++;
	//	modelMaster.add(Con25_hX);
	//	Con25_hX_n.add(Con25_hX);
	//	expr.end();
	//}

	//-------------------------- Constraint Con26_YY_ijkr -------------------------
	for (i = 1; i < imax; i++) {
		IloRangeMatrix3x3 Con26_YY_jkr(env, 0);
		for (j = 1; j < jmax; j++) {
			if (j != i && e_i[j] + s_i[j] + TravelTimeMinimum_ij[j][jmax] - (l_i[i] - TravelTimeMinimum_ij[0][i] - lamda * (s_i[j] + s_i[i])) > MaxTripDuration) {
				IloRangeMatrix2x2 Con26_YY_kr(env, 0);
				for (k = 0; k < kmax; k++) {
					IloRangeArray Con26_YY_r(env, 0);
					for (r = 0; r < rmax; r++) {
						IloExpr expr(env, 0);
						expr += Y_ikr[i][k][r] + Y_ikr[j][k][r];
						sprintf(CharMasterCon, "Con26_YY_ijkr(i%d,j%d,k%d,r%d)", i, j, k, r);
						LBMasterCon = -IloInfinity, UBMasterCon = 1;
						IloRange Con26_YY(env, LBMasterCon, expr, UBMasterCon, CharMasterCon);
						NoOfMasterCons++;
						modelMaster.add(Con26_YY);
						Con26_YY_r.add(Con26_YY);
						expr.end();
					}
					Con26_YY_kr.add(Con26_YY_r);
				}
				Con26_YY_jkr.add(Con26_YY_kr);
			}
		}
		Con26_YY_ijkr.add(Con26_YY_jkr);
	}

	//-------------------------- Constraint Con27_hX_n -------------------------
	//for (n = 0; n < 1; n++) {
	//	IloExpr expr(env, 0);
	//	expr += Heta_k[n];
	//	for (i = 1; i < imax; i++) {
	//		for (k = 0; k < kmax; k++) {
	//			for (r = 0; r < rmax; r++) {
	//				for (m = 0; m < mmax; m++) {
	//					expr -= g * X_ijkrm[i][jmax][k][r][m] * (TravelTimeMinimum_ijm[i][jmax][m] + e_i[i] + s_i[i]);//
	//					for (j = 0; j < jmax; j++) {
	//						expr -= g * X_ijkrm[j][i][k][r][m] * (TravelTimeMinimum_ijm[j][i][m] + e_i[j] + s_i[j] - e_i[i]);//
	//					}
	//				}
	//			}
	//		}
	//	}
	//	sprintf(CharMasterCon, "Con27_hX_n(n%d)", n);
	//	LBMasterCon = 0, UBMasterCon = IloInfinity;
	//	IloRange Con27_hX(env, LBMasterCon, expr, UBMasterCon, CharMasterCon);
	//	NoOfMasterCons++;
	//	modelMaster.add(Con27_hX);
	//	Con27_hX_n.add(Con27_hX);
	//	expr.end();
	//}

	//-------------------------- Constraint Con28_Y_kr -------------------------
	for (k = 0; k < kmax; k++) {
		IloRangeArray Con28_Y_r(env, 0);
		for (r = 0; r < rmax; r++) {
			IloExpr expr(env, 0);
			expr += Y_ikr[0][k][r];
			for (i = 1; i < imax; i++) {
				expr -= Y_ikr[i][k][r] / (imax + 1);
			}
			sprintf(CharMasterCon, "Con28_Y_kr(k%d,r%d)", k, r);
			LBMasterCon = 0, UBMasterCon = IloInfinity;
			IloRange Con28_Y(env, LBMasterCon, expr, UBMasterCon, CharMasterCon);
			NoOfMasterCons++;
			modelMaster.add(Con28_Y);
			Con28_Y_r.add(Con28_Y);
			expr.end();
		}
		Con28_Y_kr.add(Con28_Y_r);
	}

	//-------------------------- Constraint Con29_XX_ijkr -------------------------
	/*for (i = 1; i < imax; i++) {
		IloRangeMatrix3x3 Con29_XX_jkr(env, 0);
		for (j = 1; j < jmax; j++) {
			if (j != i) {
				IloRangeMatrix2x2 Con29_XX_kr(env, 0);
				for (k = 0; k < kmax; k++) {
					IloRangeArray Con29_XX_r(env, 0);
					for (r = 0; r < rmax; r++) {
						IloExpr expr(env, 0);
						for (m = 0; m < mmax; m++) {
							expr += X_ijkrm[i][j][k][r][m] + X_ijkrm[j][i][k][r][m];
						}
						sprintf(CharMasterCon, "Con29_XX_ijkr(i%d,j%d,k%d,r%d)", i, j, k, r);
						LBMasterCon = -IloInfinity, UBMasterCon = 1;
						IloRange Con29_XX(env, LBMasterCon, expr, UBMasterCon, CharMasterCon);
						NoOfMasterCons++;
						modelMaster.add(Con29_XX);
						Con29_XX_r.add(Con29_XX);
						expr.end();
					}
					Con29_XX_kr.add(Con29_XX_r);
				}
				Con29_XX_jkr.add(Con29_XX_kr);
			}
		}
		Con29_XX_ijkr.add(Con29_XX_jkr);
	}*/

	//-------------------------- Constraint Con30_XXX_ijlkr -------------------------
	/*for (i = 1; i < imax; i++) {
		IloRangeMatrix4x4 Con30_XXX_jlkr(env, 0);
		for (j = 1; j < jmax; j++) {
			if (j != i) {
				IloRangeMatrix3x3 Con30_XXX_lkr(env, 0);
				for (int l = 1; l < imax; l++) {
					if (l != j && l != i) {
						IloRangeMatrix2x2 Con30_XXX_kr(env, 0);
						for (k = 0; k < kmax; k++) {
							IloRangeArray Con30_XXX_r(env, 0);
							for (r = 0; r < rmax; r++) {
								IloExpr expr(env, 0);
								for (m = 0; m < mmax; m++) {
									expr += X_ijkrm[i][j][k][r][m] + X_ijkrm[j][i][k][r][m] + X_ijkrm[i][l][k][r][m] + X_ijkrm[l][i][k][r][m] + X_ijkrm[l][j][k][r][m] + X_ijkrm[j][l][k][r][m];
								}
								sprintf(CharMasterCon, "Con30_XXX_ijlkr(i%d,j%d,l%d,k%d,r%d)", i, j, l, k, r);
								LBMasterCon = -IloInfinity, UBMasterCon = 2;
								IloRange Con30_XXX(env, LBMasterCon, expr, UBMasterCon, CharMasterCon);
								NoOfMasterCons++;
								modelMaster.add(Con30_XXX);
								Con30_XXX_r.add(Con30_XXX);
								expr.end();
							}
							Con30_XXX_kr.add(Con30_XXX_r);
						}
						Con30_XXX_lkr.add(Con30_XXX_kr);
					}
				}
				Con30_XXX_jlkr.add(Con30_XXX_lkr);
			}
		}
		Con30_XXX_ijlkr.add(Con30_XXX_jlkr);
	}*/

	//-------------------------- Constraint Con31_XX_ijlm -------------------------
	for (i = 1; i < imax; i++) {
		IloRangeMatrix3x3 Con31_XX_jlm(env, 0);
		for (j = 1; j < jmax; j++) {
			if (j != i) {
				IloRangeMatrix2x2 Con31_XX_lm(env, 0);
				for (int l = 1; l < imax; l++) {
					if (l != j && l != i) {
						IloRangeArray Con31_XX_m(env, 0);
						for (m = 0; m < mmax; m++) {
							if (l_i[j] < e_i[i] + TravelTimeMinimum_ijm[i][l][m] + s_i[i] + TravelTimeMinimum_ijm[l][j][m] + s_i[l]) {
								IloExpr expr(env, 0);
								for (k = 0; k < kmax; k++) {
									for (r = 0; r < rmax; r++) {
										expr += X_ijkrm[i][l][k][r][m] + X_ijkrm[l][j][k][r][m];
									}
								}
								sprintf(CharMasterCon, "Con31_XX_ijlm(i%d,j%d,l%d,m%d)", i, j, l, m);
								LBMasterCon = -IloInfinity, UBMasterCon = 1;
								IloRange Con31_XX(env, LBMasterCon, expr, UBMasterCon, CharMasterCon);
								NoOfMasterCons++;
								modelMaster.add(Con31_XX);
								Con31_XX_m.add(Con31_XX);
								expr.end();
							}
						}
						Con31_XX_lm.add(Con31_XX_m);
					}
				}
				Con31_XX_jlm.add(Con31_XX_lm);
			}
		}
		Con31_XX_ijlm.add(Con31_XX_jlm);
	}

	//-------------------------- Constraint Con32_XY_kr -------------------------
	for (k = 0; k < kmax; k++) {
		IloRangeArray Con32_XY_r(env, 0);
		for (r = 0; r < rmax; r++) {
			IloExpr expr(env, 0);
			for (m = 0; m < mmax; m++) {
				for (i = 0; i < imax; i++) {
					for (j = 1; j < jmax + 1; j++) {
						if (j != i) {
							expr += (TravelTimeMinimum_ijm[i][j][m] + s_i[i]) * X_ijkrm[i][j][k][r][m];
						}
					}
				}
			}
			for (j = 1; j < jmax; j++) {
				expr += lamda * s_i[j] * Y_ikr[j][k][r];
			}
			sprintf(CharMasterCon, "Con32_XY_kr(k%d,r%d)", k, r);
			LBMasterCon = -IloInfinity, UBMasterCon = MaxTripDuration;
			IloRange Con32_XY(env, LBMasterCon, expr, UBMasterCon, CharMasterCon);
			NoOfMasterCons++;
			modelMaster.add(Con32_XY);
			Con32_XY_r.add(Con32_XY);
			expr.end();
		}
		Con32_XY_kr.add(Con32_XY_r);
	}




	//-------------------------- Constraint Con18_Y_kr -------------------------
	/*for (k = 0; k < kmax; k++) {
		IloRangeArray Con18_Y_r(env, 0);
		for (r = 0; r < rmax; r++) {
			IloExpr expr(env, 0);
			for (i = 1; i < imax; i++) {
				for (j = 1; j < jmax; j++) {
					for (m = 0; m < mmax; m++) {
						expr -= Small_M * X_ijkrm[i][j][k][r][m];
					}
				}
			}
			expr += Y_ikr[0][k][r];
			sprintf(CharMasterCon, "Con18_Y_kr(k%d,r%d)", k, r);
			LBMasterCon = 0, UBMasterCon = IloInfinity;
			IloRange Con18_Y(env, LBMasterCon, expr, UBMasterCon, CharMasterCon);
			NoOfMasterCons++;
			modelMaster.add(Con18_Y);
			Con18_Y_r.add(Con18_Y);
			expr.end();
		}
		Con18_Y_kr.add(Con18_Y_r);
	}*/

	//-------------------------- Constraint Con19_Y_kr -------------------------
	/*for (k = 0; k < kmax; k++) {
		IloRangeArray Con19_Y_r(env, 0);
		for (r = 0; r < rmax; r++) {
			IloExpr expr(env, 0);
			expr += Y_ikr[0][k][r]- Y_ikr[imax][k][r];
			sprintf(CharMasterCon, "Con19_Y_kr(k%d,r%d)", k, r);
			LBMasterCon = 0, UBMasterCon = Q;
			IloRange Con19_Y(env, LBMasterCon, expr, UBMasterCon, CharMasterCon);
			NoOfMasterCons++;
			modelMaster.add(Con19_Y);
			Con19_Y_r.add(Con19_Y);
			expr.end();
		}
		Con19_Y_kr.add(Con19_Y_r);
	}*/

	//-------------------------- Constraint ConSEC_ijkr -------------------------
	for (i = 1; i < imax; i++) {
		IloRangeMatrix3x3 ConSEC_jkr(env, 0);
		for (j = 1; j < jmax; j++) {
			if (i != j) {
				IloRangeMatrix2x2 ConSEC_kr(env, 0);
				for (k = 0; k < kmax; k++) {
					IloRangeArray ConSEC_r(env, 0);
					for (r = 0; r < rmax; r++) {
						IloExpr expr(env, 0);
						for (m = 0; m < mmax; m++) {
							expr += X_ijkrm[i][j][k][r][m] * (imax);
						}
						expr += U_ikr[i][k][r] - U_ikr[j][k][r] - imax + 1;
						sprintf(CharMasterCon, "ConSEC_ijkrm(i%d,j%d,k%d,r%d,m%d)", i, j, k, r, m);
						LBMasterCon = -IloInfinity, UBMasterCon = 0;
						IloRange ConSEC(env, LBMasterCon, expr, UBMasterCon, CharMasterCon);
						NoOfMasterCons++;
						modelMaster.add(ConSEC);
						ConSEC_r.add(ConSEC);
						expr.end();
					}
					ConSEC_kr.add(ConSEC_r);
				}
				ConSEC_jkr.add(ConSEC_kr);
			}
		}
		ConSEC_ijkr.add(ConSEC_jkr);
	}

	//-------------------------- Constraint ConAuxiliary_i -------------------------
	for (i = 0; i < imax + 1; i++) {
		IloExpr expr(env, 0);
		for (k = 0; k < kmax; k++) {
			for (r = 0; r < rmax; r++) {
				for (m = 0; m < mmax; m++) {
					expr += X_ijkrm[i][i][k][r][m];
					expr += X_ijkrm[0][imax][k][r][m];
					expr += X_ijkrm[imax][0][k][r][m];
					expr += X_ijkrm[i][0][k][r][m];
					expr += X_ijkrm[imax][i][k][r][m];
				}
			}
		}
		sprintf(CharMasterCon, "ConAuxiliary_i(i%d)", i);
		LBMasterCon = 0, UBMasterCon = 0;
		IloRange ConAuxiliary(env, LBMasterCon, expr, UBMasterCon, CharMasterCon);
		//NoOfMasterCons++;
		modelMaster.add(ConAuxiliary);
		ConAuxiliary_i.add(ConAuxiliary);
		expr.end();
	}


	//-------------------------- Constraint ConAuxiliary2_n -------------------------
	for (k = 0; k < kmax; k++) {
		IloExpr expr(env, 0);
		expr += Heta_k[k];
		sprintf(CharMasterCon, "ConAuxiliary2_k(k%d)", k);
		LBMasterCon = 0, UBMasterCon = IloInfinity;
		IloRange ConAuxiliary2(env, LBMasterCon, expr, UBMasterCon, CharMasterCon);
		//NoOfMasterCons++;
		modelMaster.add(ConAuxiliary2);
		ConAuxiliary2_n.add(ConAuxiliary2);
		expr.end();
	}

	//-----------------------------------------------------------------------------
	//-------------------------Finish of Master Constraints-----------------------------------------

	//------------------------------------------------------------------------------
	//------------------------------------------------------------------------------
	//---------------------------------Objective Function of master problem--------------------------
	//------------------------------------------------------------------------------
	IloExpr expr1(env);
	for (k = 0; k < kmax; k++) {
		for (r = 0; r < rmax; r++) {
			for (m = 0; m < mmax; m++) {
				for (i = 0; i < imax; i++) {
					for (j = 1; j < jmax + 1; j++) {
						expr1 += Distance_ij[i][j] * X_ijkrm[i][j][k][r][m];
						//expr1 += f * X_ijkrm[0][j][k][r][m];
					}
				}
			}
			//expr1 += g * ZZ_ikr[imax][k][r];
		}
	}

	for (k = 0; k < kmax; k++) {
		expr1 += Heta_k[k];
	}

	modelMaster.add(IloMinimize(env, expr1));
	expr1.end();

	return 0;
}
int do_slave(IloEnv env, IloModel modelSlave, IloNumVarMatrix2x2 ZZ_ir, IloRangeMatrix4x4 Con9_ZZZX_ijrm, IloRangeMatrix2x2 Con10a_ZZY_ir, IloRangeMatrix2x2 Con10b_ZZY_ir, IloRangeMatrix4x4 Con11a_ZX_ijrm, IloRangeMatrix4x4 Con11b_ZX_ijrm, IloRangeArray Con12_ZZY_n, IloRangeArray Con13_ZZY_r, IloRangeArray Con14_ZZY_r) {
	char CharSlaveVar[60];
	char CharSlaveCon[60];
	double LBSlaveCon = 0;
	double UBSlaveCon = 0;
	NoOfSlaveVars = 0;
	NoOfSlaveCons = 0;
	//--------------------------- PRIMAL SLAVE PROBLEM ----------------------------------
	//------------------------------------------------------------------------------
	//--------------------------- Primal Slave variables ---------------------------
	//-------------- Decision Variable ZZ_ir ---------------------------------------
	for (i = 0; i < imax + 1; i++) {
		IloNumVarArray ZZ_r(env, 0);
		for (r = 0; r < rmax; r++) {
			sprintf(CharSlaveVar, "ZZ_ir(i%d,r%d)", i, r);
			IloNumVar ZZ(env, 0, IloInfinity, ILOFLOAT, CharSlaveVar);
			NoOfSlaveVars++;
			ZZ_r.add(ZZ);
		}
		ZZ_ir.add(ZZ_r);
	}

	//-------------- Decision Variable Z_ijkrm ---------------------------------------
	/*for (i = 0; i < imax + 1; i++) {
		IloNumVarMatrix4x4 Z_jkrm(env, 0);
		for (j = 0; j < jmax + 1; j++) {
			IloNumVarMatrix3x3 Z_krm(env, 0);
			for (k = 0; k < kmax; k++) {
				IloNumVarMatrix2x2 Z_rm(env, 0);
				for (r = 0; r < rmax; r++) {
					IloNumVarArray Z_m(env, 0);
					for (m = 0; m < mmax; m++) {
						sprintf(CharMasterVar, "Z_ijkrm(i%d,j%d,k%d,r%d,m%d)", i, j, k, r, m);
						IloNumVar Z(env, 0, IloInfinity, ILOFLOAT, CharMasterVar);
						NoOfMasterVars++;
						Z_m.add(Z);
					}
					Z_rm.add(Z_m);
				}
				Z_krm.add(Z_rm);
			}
			Z_jkrm.add(Z_krm);
		}
		Z_ijkrm.add(Z_jkrm);
	}*/







	//-----------------  Finish of Primal Slave variables ------------------
	//-----------------------------------------------------------------------------
	//------------------------- Slave Primal  Constraintes ------------------------
	//-----------------------------------------------------------------------------
	//-------------------------- Constraint Con7_ZZZ_ikr -------------------------
	/*for (i = 0; i < imax; i++) {
		IloRangeMatrix2x2 Con7_ZZZ_kr(env, 0);
		for (k = 0; k < kmax; k++) {
			IloRangeArray Con7_ZZZ_r(env, 0);
			for (r = 0; r < rmax; r++) {
				IloExpr expr(env, 0);
				for (j = 1; j < jmax + 1; j++) {
					if (j != i) {
						for (m = 0; m < mmax; m++) {
							expr -= Z_ijkrm[i][j][k][r][m];
						}
					}
				}
				expr += ZZ_ikr[i][k][r];
				sprintf(CharMasterCon, "Con7_ZZZ_ikr(i%d,k%d,r%d)", i, k, r);
				LBMasterCon = 0, UBMasterCon = 0;
				IloRange Con7_ZZZ(env, LBMasterCon, expr, UBMasterCon, CharMasterCon);
				NoOfMasterCons++;
				modelMaster.add(Con7_ZZZ);
				Con7_ZZZ_r.add(Con7_ZZZ);
				expr.end();
			}
			Con7_ZZZ_kr.add(Con7_ZZZ_r);
		}
		Con7_ZZZ_ikr.add(Con7_ZZZ_kr);
	}*/

	//-------------------------- Constraint Con8_ZZZ_kr -------------------------
	/*for (k = 0; k < kmax; k++) {
		IloRangeArray Con8_ZZZ_r(env, 0);
		for (r = 0; r < rmax; r++) {
			IloExpr expr(env, 0);
			for (i = 0; i < imax; i++) {
				for (m = 0; m < mmax; m++) {
					expr -= (1 + theta_ijm[i][jmax][m]) * Z_ijkrm[i][jmax][k][r][m] + zeta_ijm[i][jmax][m] * X_ijkrm[i][jmax][k][r][m];
				}
			}
			expr += ZZ_ikr[imax][k][r];
			sprintf(CharMasterCon, "Con8_ZZZ_kr(k%d,r%d)", k, r);
			LBMasterCon = 0, UBMasterCon = 0;
			IloRange Con8_ZZZ(env, LBMasterCon, expr, UBMasterCon, CharMasterCon);
			NoOfMasterCons++;
			modelMaster.add(Con8_ZZZ);
			Con8_ZZZ_r.add(Con8_ZZZ);
			expr.end();
		}
		Con8_ZZZ_kr.add(Con8_ZZZ_r);
	}*/

	//-------------------------- Constraint Con9_ZZZX_ijrm -------------------------
	for (i = 0; i < imax; i++) {
		IloRangeMatrix3x3 Con9_ZZZX_jrm(env, 0);
		for (j = 1; j < jmax + 1; j++) {
			IloRangeMatrix2x2 Con9_ZZZX_rm(env, 0);
			for (r = 0; r < rmax; r++) {
				IloRangeArray Con9_ZZZX_m(env, 0);
				for (m = 0; m < mmax; m++) {
					IloExpr expr(env, 0);
					expr -= (1 + theta_ijm[i][j][m]) * ZZ_ir[i][r] - ZZ_ir[j][r];// (DayDuration + theta_ijm[i][j][m] * DayDuration + zeta_ijm[i][j][m] + s_i[j]);
					sprintf(CharSlaveCon, "Con9_ZZZX_ijrm(i%d,j%d,r%d,m%d)", i, j, r, m);
					LBSlaveCon = -((1 - X_ijrmValue[i][j][r][m]) * Big_M - zeta_ijm[i][j][m] - s_i[j]), UBSlaveCon = IloInfinity;
					IloRange Con9_ZZZX(env, LBSlaveCon, expr, UBSlaveCon, CharSlaveCon);
					NoOfSlaveCons++;
					modelSlave.add(Con9_ZZZX);
					Con9_ZZZX_m.add(Con9_ZZZX);
					expr.end();
				}
				Con9_ZZZX_rm.add(Con9_ZZZX_m);
			}
			Con9_ZZZX_jrm.add(Con9_ZZZX_rm);
		}
		Con9_ZZZX_ijrm.add(Con9_ZZZX_jrm);
	}

	//-------------------------- Constraint Con10a_ZZY_ir -------------------------
	for (i = 0; i < imax + 1; i++) {
		IloRangeArray Con10a_ZZY_r(env, 0);
		for (r = 0; r < rmax; r++) {
			IloExpr expr(env, 0);
			expr += ZZ_ir[i][r];
			sprintf(CharSlaveCon, "Con10a_ZZY_ir(i%d,r%d)", i, r);
			LBSlaveCon = (e_i[i] + s_i[i]) * Y_irValue[i][r], UBSlaveCon = IloInfinity;
			IloRange Con10a_ZZY(env, LBSlaveCon, expr, UBSlaveCon, CharSlaveCon);
			NoOfSlaveCons++;
			modelSlave.add(Con10a_ZZY);
			Con10a_ZZY_r.add(Con10a_ZZY);
			expr.end();
		}
		Con10a_ZZY_ir.add(Con10a_ZZY_r);
	}

	//-------------------------- Constraint Con10b_ZZY_ir -------------------------
	for (i = 0; i < imax + 1; i++) {
		IloRangeArray Con10b_ZZY_r(env, 0);
		for (r = 0; r < rmax; r++) {
			IloExpr expr(env, 0);
			expr -= ZZ_ir[i][r];
			sprintf(CharSlaveCon, "Con10b_ZZY_ir(i%d,r%d)", i, r);
			LBSlaveCon = -(l_i[i] + s_i[i]) * Y_irValue[i][r], UBSlaveCon = IloInfinity;
			IloRange Con10b_ZZY(env, LBSlaveCon, expr, UBSlaveCon, CharSlaveCon);
			NoOfSlaveCons++;
			modelSlave.add(Con10b_ZZY);
			Con10b_ZZY_r.add(Con10b_ZZY);
			expr.end();
		}
		Con10b_ZZY_ir.add(Con10b_ZZY_r);
	}

	//-------------------------- Constraint Con11a_ZX_ijrm -------------------------
	for (i = 0; i < imax + 1; i++) {
		IloRangeMatrix3x3 Con11a_ZX_jrm(env, 0);
		for (j = 0; j < jmax + 1; j++) {
			IloRangeMatrix2x2 Con11a_ZX_rm(env, 0);
			for (r = 0; r < rmax; r++) {
				IloRangeArray Con11a_ZX_m(env, 0);
				for (m = 1; m < mmax; m++) {
					IloExpr expr(env, 0);
					expr += ZZ_ir[i][r];//DayDuration
					sprintf(CharSlaveCon, "Con11a_ZX_ijrm(i%d,j%d,r%d,m%d)", i, j, r, m);
					LBSlaveCon = w_ijm[i][j][m - 1] * X_ijrmValue[i][j][r][m] - (1 - X_ijrmValue[i][j][r][m]) * Big_M, UBSlaveCon = IloInfinity;
					IloRange Con11a_ZX(env, LBSlaveCon, expr, UBSlaveCon, CharSlaveCon);
					NoOfSlaveCons++;
					modelSlave.add(Con11a_ZX);
					Con11a_ZX_m.add(Con11a_ZX);
					expr.end();
				}
				Con11a_ZX_rm.add(Con11a_ZX_m);
			}
			Con11a_ZX_jrm.add(Con11a_ZX_rm);
		}
		Con11a_ZX_ijrm.add(Con11a_ZX_jrm);

	}

	//-------------------------- Constraint Con11b_ZX_ijrm -------------------------
	for (i = 0; i < imax + 1; i++) {
		IloRangeMatrix3x3 Con11b_ZX_jrm(env, 0);
		for (j = 0; j < jmax + 1; j++) {
			IloRangeMatrix2x2 Con11b_ZX_rm(env, 0);
			for (r = 0; r < rmax; r++) {
				IloRangeArray Con11b_ZX_m(env, 0);
				for (m = 0; m < mmax; m++) {
					IloExpr expr(env, 0);
					expr -= ZZ_ir[i][r];//DayDuration
					sprintf(CharSlaveCon, "Con11b_ZX_ijrm(i%d,j%d,r%d,m%d)", i, j, r, m);
					LBSlaveCon = -(w_ijm[i][j][m] * X_ijrmValue[i][j][r][m] + (1 - X_ijrmValue[i][j][r][m]) * Big_M), UBSlaveCon = IloInfinity;
					IloRange Con11b_ZX(env, LBSlaveCon, expr, UBSlaveCon, CharSlaveCon);
					NoOfSlaveCons++;
					modelSlave.add(Con11b_ZX);
					Con11b_ZX_m.add(Con11b_ZX);
					expr.end();
				}
				Con11b_ZX_rm.add(Con11b_ZX_m);
			}
			Con11b_ZX_jrm.add(Con11b_ZX_rm);
		}
		Con11b_ZX_ijrm.add(Con11b_ZX_jrm);
	}

	//-------------------------- Constraint Con12_ZZY_n -------------------------
	for (n = 0; n < 1; n++) {
		IloExpr expr(env, 0);
		expr += ZZ_ir[0][0];
		double Sum_lamda_s_Y = 0;
		for (i = 1; i < imax; i++) {
			Sum_lamda_s_Y += lamda * s_i[i] * Y_irValue[i][0];
		}
		sprintf(CharSlaveCon, "Con12_ZZY_n(n%d)", n);
		LBSlaveCon = Sum_lamda_s_Y, UBSlaveCon = IloInfinity;
		IloRange Con12_ZZY(env, LBSlaveCon, expr, UBSlaveCon, CharSlaveCon);
		NoOfSlaveCons++;
		modelSlave.add(Con12_ZZY);
		Con12_ZZY_n.add(Con12_ZZY);
		expr.end();
	}

	//-------------------------- Constraint Con13_ZZY_r -------------------------
	for (r = 1; r < rmax; r++) {
		IloExpr expr(env, 0);
		expr += ZZ_ir[0][r] - ZZ_ir[imax][r - 1];
		double Sum_lamda_s_Y = 0;
		for (i = 1; i < imax; i++) {
			Sum_lamda_s_Y += lamda * s_i[i] * Y_irValue[i][r];
		}
		sprintf(CharSlaveCon, "Con13_ZZY_r(r%d)", r);
		LBSlaveCon = Sum_lamda_s_Y, UBSlaveCon = IloInfinity;
		IloRange Con13_ZZY(env, LBSlaveCon, expr, UBSlaveCon, CharSlaveCon);
		NoOfSlaveCons++;
		modelSlave.add(Con13_ZZY);
		Con13_ZZY_r.add(Con13_ZZY);
		expr.end();
	}


	//-------------------------- Constraint Con14_ZZY_r -------------------------
	for (r = 0; r < rmax; r++) {
		IloExpr expr(env, 0);
		expr -= ZZ_ir[imax][r] - ZZ_ir[0][r];
		double Sum_lamda_s_Y = 0;
		for (i = 1; i < imax; i++) {
			Sum_lamda_s_Y -= lamda * s_i[i] * Y_irValue[i][r];
		}
		Sum_lamda_s_Y += MaxTripDuration;
		sprintf(CharSlaveCon, "Con14_ZZY_r(r%d)", r);
		LBSlaveCon = -Sum_lamda_s_Y, UBSlaveCon = IloInfinity;
		IloRange Con14_ZZY(env, LBSlaveCon, expr, UBSlaveCon, CharSlaveCon);
		NoOfSlaveCons++;
		modelSlave.add(Con14_ZZY);
		Con14_ZZY_r.add(Con14_ZZY);
		expr.end();
	}

	//------------------------------------------------------------------------------
	//------------------------------------------------------------------------------
	//---------------------------------Objective function of PSP--------------------------
	//------------------------------------------------------------------------------
	/*IloExpr expr_slave(env);
	for (r = 0; r < rmax; r++) {
		expr_slave += g * ZZ_ir[imax][r];
	}
	modelSlave.add(IloMinimize(env, expr_slave));
	expr_slave.end();*/

	return 0;
}
int do_aux_slave(IloEnv env, IloModel modelAuxSlave, IloNumVarMatrix3x3 X_aux_ijm, IloNumVarArray ZZ_aux_i, IloRangeArray Con2_aux_YX_n, IloRangeArray Con3_aux_YX_n, IloRangeArray Con4a_aux_YX_i, IloRangeArray Con4b_aux_YX_i, IloRangeMatrix3x3 Con9_aux_ZZZX_ijm, IloRangeArray Con10a_aux_ZZY_i, IloRangeArray Con10b_aux_ZZY_i, IloRangeMatrix3x3 Con11a_aux_ZX_ijm, IloRangeMatrix3x3 Con11b_aux_ZX_ijm, IloRangeArray Con14_aux_ZZY_n) {

	char CharAuxSlaveVar[60];
	char CharAuxSlaveCon[60];
	double LBAuxSlaveCon = 0;
	double UBAuxSlaveCon = 0;
	//NoOfMasterVars = 0;
	//NoOfMasterCons = 0;
	//------------------------------------------------------------------------------
	//---------------------------------- MASTER ------------------------------------
	//------------------------------------------------------------------------------
	//----------------------------- Auxiliary Variable --------------------------------
	//-------------- Decision Variable X_aux_ijm ---------------------------------------
	for (i = 0; i < imax + 1; i++) {
		IloNumVarMatrix2x2 X_aux_jm(env, 0);
		for (j = 0; j < jmax + 1; j++) {
			IloNumVarArray X_aux_m(env, 0);
			for (m = 0; m < mmax; m++) {
				sprintf(CharAuxSlaveVar, "X_aux_ijm(i%d,j%d,m%d)", i, j, m);
				IloNumVar X_aux(env, 0, 1, ILOINT, CharAuxSlaveVar);
				//NoOfMasterVars++;
				X_aux_m.add(X_aux);
			}
			X_aux_jm.add(X_aux_m);
		}
		X_aux_ijm.add(X_aux_jm);
	}

	//-------------- Decision Variable ZZ_aux_i ---------------------------------------
	for (i = 0; i < imax + 1; i++) {
		sprintf(CharAuxSlaveVar, "ZZ_aux_i(i%d)", i);
		IloNumVar ZZ_aux(env, 0, IloInfinity, ILOFLOAT, CharAuxSlaveVar);
		//NoOfSlaveVars++;
		ZZ_aux_i.add(ZZ_aux);
	}


	//-----------------------------Finish of Auxiliary Variables --------------------------------

	//-----------------------------------------------------------------------------
	//-------------------------Start of Auxiliary Constraints-----------------------------------------
	//------------------------------------------------------------------------------
	//------------------------------------------------------------------------------

	//-------------------------- Constraint Con2_aux_YX_n -------------------------
	for (n = 0; n < 1; n++) {
		IloExpr expr(env, 0);
		for (j = 1; j < jmax; j++) {
			for (m = 0; m < mmax; m++) {
				expr += X_aux_ijm[0][j][m];
			}
		}
		//expr += Y_ikr[0][k][r];
		sprintf(CharAuxSlaveCon, "Con2_aux_YX_n(n%d)", n);
		LBAuxSlaveCon = 0, UBAuxSlaveCon = 0;
		IloRange Con2_aux_YX(env, LBAuxSlaveCon, expr, UBAuxSlaveCon, CharAuxSlaveCon);
		//NoOfMasterCons++;
		modelAuxSlave.add(Con2_aux_YX);
		Con2_aux_YX_n.add(Con2_aux_YX);
		expr.end();
	}

	//-------------------------- Constraint Con3_aux_YX_n -------------------------
	for (n = 0; n < 1; n++) {
		IloExpr expr(env, 0);
		for (j = 1; j < jmax; j++) {
			for (m = 0; m < mmax; m++) {
				expr += X_aux_ijm[j][imax][m];
			}
		}
		//expr += Y_ikr[imax][k][r];
		sprintf(CharAuxSlaveCon, "Con3_aux_YX_n(n%d)", n);
		LBAuxSlaveCon = 0, UBAuxSlaveCon = 0;
		IloRange Con3_aux_YX(env, LBAuxSlaveCon, expr, UBAuxSlaveCon, CharAuxSlaveCon);
		//NoOfMasterCons++;
		modelAuxSlave.add(Con3_aux_YX);
		Con3_aux_YX_n.add(Con3_aux_YX);
		expr.end();
	}

	//-------------------------- Constraint Con4a_aux_YX_i -------------------------
	for (i = 1; i < imax; i++) {
		IloExpr expr(env, 0);
		for (j = 0; j < jmax; j++) {
			if (j != i) {
				for (m = 0; m < mmax; m++) {
					expr += X_aux_ijm[j][i][m];
				}
			}
		}
		//expr += Y_ikr[i][k][r];
		sprintf(CharAuxSlaveCon, "Con4a_aux_YX_i(i%d)", i);
		LBAuxSlaveCon = 0, UBAuxSlaveCon = 0;
		IloRange Con4a_aux_YX(env, LBAuxSlaveCon, expr, UBAuxSlaveCon, CharAuxSlaveCon);
		//NoOfMasterCons++;
		modelAuxSlave.add(Con4a_aux_YX);
		Con4a_aux_YX_i.add(Con4a_aux_YX);
		expr.end();

	}

	//-------------------------- Constraint Con4b_aux_YX_i -------------------------
	for (i = 1; i < imax; i++) {
		IloExpr expr(env, 0);
		//expr += Y_ikr[i][k][r];
		for (j = 1; j < jmax + 1; j++) {
			if (j != i) {
				for (m = 0; m < mmax; m++) {
					expr += X_aux_ijm[i][j][m];
				}
			}
		}
		sprintf(CharAuxSlaveCon, "Con4b_aux_YX_i(i%d)", i);
		LBAuxSlaveCon = 0, UBAuxSlaveCon = 0;
		IloRange Con4b_aux_YX(env, LBAuxSlaveCon, expr, UBAuxSlaveCon, CharAuxSlaveCon);
		//NoOfMasterCons++;
		modelAuxSlave.add(Con4b_aux_YX);
		Con4b_aux_YX_i.add(Con4b_aux_YX);
		expr.end();

	}

	//-------------------------- Constraint Con9_aux_ZZZX_ijm -------------------------
	for (i = 0; i < imax; i++) {
		IloRangeMatrix2x2 Con9_aux_ZZZX_jm(env, 0);
		for (j = 1; j < jmax + 1; j++) {
			IloRangeArray Con9_aux_ZZZX_m(env, 0);
			for (m = 0; m < mmax; m++) {
				IloExpr expr(env, 0);
				expr -= (1 + theta_ijm[i][j][m]) * ZZ_aux_i[i] - ZZ_aux_i[j];// (DayDuration + theta_ijm[i][j][m] * DayDuration + zeta_ijm[i][j][m] + s_i[j]);
				expr += ((1 - X_aux_ijm[i][j][m]) * Big_M - zeta_ijm[i][j][m] - s_i[j]);
				sprintf(CharAuxSlaveCon, "Con9_aux_ZZZX_ijm(i%d,j%d,m%d)", i, j, m);
				LBAuxSlaveCon = 0, UBAuxSlaveCon = IloInfinity;
				IloRange Con9_aux_ZZZX(env, LBAuxSlaveCon, expr, UBAuxSlaveCon, CharAuxSlaveCon);
				//NoOfSlaveCons++;
				modelAuxSlave.add(Con9_aux_ZZZX);
				Con9_aux_ZZZX_m.add(Con9_aux_ZZZX);
				expr.end();
			}
			Con9_aux_ZZZX_jm.add(Con9_aux_ZZZX_m);
		}
		Con9_aux_ZZZX_ijm.add(Con9_aux_ZZZX_jm);
	}

	//-------------------------- Constraint Con10a_aux_ZZY_i -------------------------
	for (i = 0; i < imax + 1; i++) {
		IloExpr expr(env, 0);
		expr += ZZ_aux_i[i];
		sprintf(CharAuxSlaveCon, "Con10a_aux_ZZY_i(i%d)", i);
		LBAuxSlaveCon = (e_i[i] + s_i[i]) * Y_iValue[i], UBAuxSlaveCon = IloInfinity;
		IloRange Con10a_aux_ZZY(env, LBAuxSlaveCon, expr, UBAuxSlaveCon, CharAuxSlaveCon);
		//NoOfSlaveCons++;
		modelAuxSlave.add(Con10a_aux_ZZY);
		Con10a_aux_ZZY_i.add(Con10a_aux_ZZY);
		expr.end();
	}

	//-------------------------- Constraint Con10b_aux_ZZY_i -------------------------
	for (i = 0; i < imax + 1; i++) {
		IloExpr expr(env, 0);
		expr -= ZZ_aux_i[i];
		sprintf(CharAuxSlaveCon, "Con10b_aux_ZZY_i(i%d)", i);
		LBAuxSlaveCon = -(l_i[i] + s_i[i]) * Y_iValue[i], UBAuxSlaveCon = IloInfinity;
		IloRange Con10b_aux_ZZY(env, LBAuxSlaveCon, expr, UBAuxSlaveCon, CharAuxSlaveCon);
		//NoOfSlaveCons++;
		modelAuxSlave.add(Con10b_aux_ZZY);
		Con10b_aux_ZZY_i.add(Con10b_aux_ZZY);
		expr.end();
	}

	//-------------------------- Constraint Con11a_aux_ZX_ijm -------------------------
	for (i = 0; i < imax + 1; i++) {
		IloRangeMatrix2x2 Con11a_aux_ZX_jm(env, 0);
		for (j = 0; j < jmax + 1; j++) {
			IloRangeArray Con11a_aux_ZX_m(env, 0);
			for (m = 1; m < mmax; m++) {
				IloExpr expr(env, 0);
				expr += ZZ_aux_i[i] - (w_ijm[i][j][m - 1] * X_aux_ijm[i][j][m] - (1 - X_aux_ijm[i][j][m]) * Big_M);//DayDuration
				sprintf(CharAuxSlaveCon, "Con11a_aux_ZX_ijm(i%d,j%d,m%d)", i, j, m);
				LBAuxSlaveCon = 0, UBAuxSlaveCon = IloInfinity;
				IloRange Con11a_aux_ZX(env, LBAuxSlaveCon, expr, UBAuxSlaveCon, CharAuxSlaveCon);
				//NoOfSlaveCons++;
				modelAuxSlave.add(Con11a_aux_ZX);
				Con11a_aux_ZX_m.add(Con11a_aux_ZX);
				expr.end();
			}
			Con11a_aux_ZX_jm.add(Con11a_aux_ZX_m);
		}
		Con11a_aux_ZX_ijm.add(Con11a_aux_ZX_jm);
	}

	//-------------------------- Constraint Con11b_aux_ZX_ijm -------------------------
	for (i = 0; i < imax + 1; i++) {
		IloRangeMatrix2x2 Con11b_aux_ZX_jm(env, 0);
		for (j = 0; j < jmax + 1; j++) {
			IloRangeArray Con11b_aux_ZX_m(env, 0);
			for (m = 0; m < mmax; m++) {
				IloExpr expr(env, 0);
				expr -= ZZ_aux_i[i];//DayDuration
				expr += (w_ijm[i][j][m] * X_aux_ijm[i][j][m] + (1 - X_aux_ijm[i][j][m]) * Big_M);//DayDuration
				sprintf(CharAuxSlaveCon, "Con11b_aux_ZX_ijm(i%d,j%d,m%d)", i, j, m);
				LBAuxSlaveCon = 0, UBAuxSlaveCon = IloInfinity;
				IloRange Con11b_aux_ZX(env, LBAuxSlaveCon, expr, UBAuxSlaveCon, CharAuxSlaveCon);
				//NoOfSlaveCons++;
				modelAuxSlave.add(Con11b_aux_ZX);
				Con11b_aux_ZX_m.add(Con11b_aux_ZX);
				expr.end();
			}
			Con11b_aux_ZX_jm.add(Con11b_aux_ZX_m);
		}
		Con11b_aux_ZX_ijm.add(Con11b_aux_ZX_jm);
	}

	//-------------------------- Constraint Con14_aux_ZZY_n -------------------------
	for (n = 0; n < 1; n++) {
		IloExpr expr(env, 0);
		expr -= ZZ_aux_i[imax] - ZZ_aux_i[0];
		double Sum_lamda_s_Y = 0;
		for (i = 1; i < imax; i++) {
			Sum_lamda_s_Y -= lamda * s_i[i] * Y_iValue[i];
		}
		Sum_lamda_s_Y += MaxTripDuration;
		sprintf(CharAuxSlaveCon, "Con14_aux_ZZY_n(n%d)", n);
		LBAuxSlaveCon = -Sum_lamda_s_Y, UBAuxSlaveCon = IloInfinity;
		IloRange Con14_aux_ZZY(env, LBAuxSlaveCon, expr, UBAuxSlaveCon, CharAuxSlaveCon);
		//NoOfSlaveCons++;
		modelAuxSlave.add(Con14_aux_ZZY);
		Con14_aux_ZZY_n.add(Con14_aux_ZZY);
		expr.end();
	}


	//-----------------------------------------------------------------------------
	//-------------------------Finish of Auxiliary Constraints-----------------------------------------

	//------------------------------------------------------------------------------
	//------------------------------------------------------------------------------
	//---------------------------------Objective Function of Auxiliary problem--------------------------
	//------------------------------------------------------------------------------
	IloExpr expr_slave(env);
	expr_slave = g * ZZ_aux_i[imax];
	modelAuxSlave.add(IloMinimize(env, expr_slave));
	expr_slave.end();

	return 0;
}
int CreateAddSECS(IloEnv env, IloModel modelMaster_ptr, int Sub_ptr, int** SubtoursNodes_ptr, int* NodesInSubtour_ptr, IloNumVarMatrix5x5 X_ijkrm, int* IsSubtourToBeEliminated_l, int loop) {
	//char CharMasterVar[60];
	char MasterCut[90];
	//bool NodeIsInSubtour = false;


	for (int l = 0; l < Sub_ptr; l++) {
		if (IsSubtourToBeEliminated_l[l] == 1) {
			IloExpr expr101(env);
			for (int n = 0; n < NodesInSubtour_ptr[l]; n++) {
				i = SubtoursNodes_ptr[l][n];
				j = SubtoursNodes_ptr[l][n + 1];
				for (k = 0; k < kmax; k++) {
					for (r = 0; r < rmax; r++) {
						for (m = 0; m < mmax; m++) {
							expr101 += X_ijkrm[i][j][k][r][m];
						}
					}
				}
			}
			expr101 -= NodesInSubtour_ptr[l] - 1;
			SECNumber++;
			sprintf(MasterCut, "SEC(iter%d, SECiter%d, subtour%d)", loop, SECIterations, SECNumber);
			double LB101 = -IloInfinity, UB101 = 0;
			IloRange SEC(env, LB101, expr101, UB101, MasterCut);
			modelMaster_ptr.add(SEC);
			expr101.end();
		}


	}
	return 0;
}
int DetectSubtoursInVRP(IloModel modelMaster_ptr, int** SubtoursNodes_ptr, int* NodesInSubtour_ptr, int* MinNodesInSubtour_ptr, int* MaxNodesInSubtour_ptr, double* SubtourDistance_ptr, double* ShortestSubtourDistance_ptr, int* Sub_ptr, int* NonSub_ptr, int** NonSubtoursNodes_ptr, int* NodesInNonSubtour_ptr) {
	SubtourDistance_ptr = new double[imax + 1];
	int LongestSubtour, ShortestSubtour, NoOfShortestSubtours, NoOfVisitedNodes = 0;
	int** SubtoursNodes_ptr_LOCAL;
	int** NonSubtoursNodes_ptr_LOCAL;
	SubtoursNodes_ptr_LOCAL = new int* [imax + 1];
	NonSubtoursNodes_ptr_LOCAL = new int* [imax + 1];
	for (i = 0; i < imax + 1; i++) {
		SubtoursNodes_ptr_LOCAL[i] = new int[imax + 1];
		NonSubtoursNodes_ptr_LOCAL[i] = new int[imax + 1];
	}

	*MaxNodesInSubtour_ptr = 0;
	*MinNodesInSubtour_ptr = imax + 1;
	bool* NodeVisited = new bool[imax + 1];
	//NodeVisited = {};
	for (i = 0; i < imax + 1; i++) {
		NodesInSubtour_ptr[i] = 0;
		SubtourDistance_ptr[i] = 0;
		NodeVisited[i] = false;
	}
	//Detect the routes starting from the depot. THESE ARE NOT SUBTOURS
	for (k = 0; k < kmax; k++) {
		for (r = 0; r < rmax; r++) {
			i = 0;//Detect the routes starting from the depot.
			*NonSub_ptr = *NonSub_ptr + 1;
			NodesInNonSubtour_ptr[*NonSub_ptr] = 0;
			NonSubtoursNodes_ptr_LOCAL[*NonSub_ptr][0] = i;
		NextNode:;
			for (j = 0; j < jmax + 1; j++) {
				if (X_ijValue[i][j] > 0.1) {
					if (NodeVisited[j] != true) {
						NodeVisited[j] = true;
						NoOfVisitedNodes++;
						//cout << "X_ij[" << i << "][" << j << "] = " << 1 << endl;
						//SubtourDistance_ptr[*Sub_ptr] = SubtourDistance_ptr[*Sub_ptr] + Distance_ij[i][j];
						//cout << "C[" << i << "][" << j << "]=" << C[i][j] << endl;
						//cout << "X_ijValue[" << i << "][" << j << "]=" << X_ijValue[i][j] << endl;
						i = j;
						NodesInNonSubtour_ptr[*NonSub_ptr]++;
						NonSubtoursNodes_ptr_LOCAL[*NonSub_ptr][NodesInNonSubtour_ptr[*NonSub_ptr]] = j;
						//cout << "SubtoursNodes[" << Sub << "][" << NodesInSubtour_ptr[Sub] << "] = " << SubtoursNodes_ptr_LOCAL[Sub][NodesInSubtour_ptr[Sub]] << endl;
						goto NextNode;
					}
				}
			}
		}
	}
	//Detect the routes starting from the ending point. THESE ARE NOT SUBTOURS
	for (k = 0; k < kmax; k++) {
		for (r = 0; r < rmax; r++) {
			i = imax;//Detect the routes starting from the ending point.
			*NonSub_ptr = *NonSub_ptr + 1;
			NodesInNonSubtour_ptr[*NonSub_ptr] = 0;
			NonSubtoursNodes_ptr_LOCAL[*NonSub_ptr][0] = i;
		NextNodeEnding:;
			for (j = 0; j < jmax + 1; j++) {
				if (X_ijValue[i][j] > 0.1) {
					if (NodeVisited[j] != true) {
						NodeVisited[j] = true;
						NoOfVisitedNodes++;
						//cout << "X_ij[" << i << "][" << j << "] = " << 1 << endl;
						//SubtourDistance_ptr[*Sub_ptr] = SubtourDistance_ptr[*Sub_ptr] + Distance_ij[i][j];
						//cout << "C[" << i << "][" << j << "]=" << C[i][j] << endl;
						//cout << "X_ijValue[" << i << "][" << j << "]=" << X_ijValue[i][j] << endl;
						i = j;
						NodesInNonSubtour_ptr[*NonSub_ptr]++;
						NonSubtoursNodes_ptr_LOCAL[*NonSub_ptr][NodesInNonSubtour_ptr[*NonSub_ptr]] = j;
						//cout << "SubtoursNodes[" << Sub << "][" << NodesInSubtour_ptr[Sub] << "] = " << SubtoursNodes_ptr_LOCAL[Sub][NodesInSubtour_ptr[Sub]] << endl;
						goto NextNodeEnding;
					}
				}
			}
		}
	}
	if (NoOfVisitedNodes < imax) {
		cout << "WE HAVE GOT SUBTOURS" << endl;
		i = 1;
		for (i = 1; i < imax + 1; i++) {
			if (NodeVisited[i] == false) {
				goto NewSubtour;
			}
		}
	NewSubtour:;
		*Sub_ptr = *Sub_ptr + 1;
		NodesInSubtour_ptr[*Sub_ptr] = 0;
		SubtoursNodes_ptr_LOCAL[*Sub_ptr][0] = i;
		//cout << "SubtoursNodes[" << Sub_ptr << "][" << NodesInSubtour_ptr[Sub_ptr] << "] = " << SubtoursNodes_ptr[Sub_ptr][NodesInSubtour_ptr[Sub_ptr]] << endl;
		//cout << "Subtours = " << Sub_ptr << endl;
	NextNodeSubtour:;
		for (j = 0; j < jmax + 1; j++) {
			if (X_ijValue[i][j] > 0.1) {
				if (NodeVisited[j] != true) {
					NodeVisited[j] = true;
					//cout << "X_ij[" << i << "][" << j << "] = " << 1 << endl;
					SubtourDistance_ptr[*Sub_ptr] = SubtourDistance_ptr[*Sub_ptr] + Distance_ij[i][j];
					//cout << "C[" << i << "][" << j << "]=" << C[i][j] << endl;
					//cout << "X_ijValue[" << i << "][" << j << "]=" << X_ijValue[i][j] << endl;
					i = j;
					NodesInSubtour_ptr[*Sub_ptr]++;
					SubtoursNodes_ptr_LOCAL[*Sub_ptr][NodesInSubtour_ptr[*Sub_ptr]] = j;

					//cout << "SubtoursNodes[" << Sub_ptr << "][" << NodesInSubtour_ptr[Sub_ptr] << "] = " << SubtoursNodes_ptr_LOCAL[Sub_ptr][NodesInSubtour_ptr[Sub_ptr]] << endl;
					goto NextNodeSubtour;
				}
				else {

					while (NodeVisited[i] == true) {
						i = i + 1;
					}
					if (i >= imax) {
						goto end;
					}
					else {
						goto NewSubtour;
					}

				}
			}

		}
	}
end:;

	if (Sub_ptr >= 0) {
		*Sub_ptr = *Sub_ptr + 1;
		//cout << "Total Number of Subtours: " << *Sub_ptr << endl;
		for (int l = 0; l < *Sub_ptr; l++) {
			for (k = 0; k <= NodesInSubtour_ptr[l]; k++) {
				SubtoursNodes_ptr[l][k] = SubtoursNodes_ptr_LOCAL[l][k];
				//cout << "SubtoursNodes[" << l << "][" << k << "] = " << SubtoursNodes_ptr[l][k] << endl;
			}
			//cout << "NodesInSubtour_ptr[" << l << "]= " << NodesInSubtour_ptr[l] << endl;
		}
	}
	int FalseNonSub_ptr = *NonSub_ptr;
	*NonSub_ptr = 0;
	for (int l = 0; l < FalseNonSub_ptr; l++) {
		if (NodesInNonSubtour_ptr[l] > 1) {
			*NonSub_ptr = *NonSub_ptr + 1;
		}
	}
	if (NonSub_ptr >= 0) {
		//cout << "Total Number of NonSubtours: " << *NonSub_ptr << endl;
		for (int l = 0; l < *NonSub_ptr; l++) {
			for (k = 0; k <= NodesInNonSubtour_ptr[l]; k++) {
				NonSubtoursNodes_ptr[l][k] = NonSubtoursNodes_ptr_LOCAL[l][k];
				//cout << "NonSubtoursNodes[" << l << "][" << k << "] = " << NonSubtoursNodes_ptr[l][k] << endl;
			}
		}
	}



	//Detect shortest subtour
	for (i = 0; i < *Sub_ptr; i++) {
		if (*MinNodesInSubtour_ptr > NodesInSubtour_ptr[i] && NodesInSubtour_ptr[i] != 0) {
			*MinNodesInSubtour_ptr = NodesInSubtour_ptr[i];
			ShortestSubtour = i;
		}
	}

	//Detect longest subtour
	for (i = 0; i < *Sub_ptr; i++) {
		if (*MaxNodesInSubtour_ptr < NodesInSubtour_ptr[i]) {
			*MaxNodesInSubtour_ptr = NodesInSubtour_ptr[i];
			LongestSubtour = i;
		}
	}

	//Detect Shortest subtour distance
	for (i = 0; i < *Sub_ptr; i++) {
		if (*ShortestSubtourDistance_ptr > SubtourDistance_ptr[i]) {
			*ShortestSubtourDistance_ptr = SubtourDistance_ptr[i];
		}
	}
	NoOfShortestSubtours = 0;
	for (i = 0; i < *Sub_ptr; i++) {
		if (SubtourDistance_ptr[i] == *ShortestSubtourDistance_ptr) {
			NoOfShortestSubtours++;
		}
	}
	/*for (l = 0; l <= Sub; l++) {
		cout << "SubtourDistance[" << l << "]=" << SubtourDistance_ptr[l] << endl;
	}*/
	//cout << "ShortestSubtourDistance=" << *ShortestSubtourDistance_ptr << endl;
	//cout << "NoOfShortestSubtours=" << NoOfShortestSubtours << endl;
	delete[] NodeVisited;

	return 0;
}
int PrintCurrentTours(int loop_ptr, char* FilePath_Results_ptr, int Sub_ptr, int** SubtoursNodes_ptr, int* NodesInSubtour_ptr, int NonSub_ptr, int** NonSubtoursNodes_ptr, int* NodesInNonSubtour_ptr, double* XCOORD_Center_l, double* YCOORD_Center_l, double* XCOORD_Center_Non_l, double* YCOORD_Center_Non_l, int* IsSubtourToBeEliminated_l) {
	int status, test = 0;
	char* FileName_ptr;
	char filepath[1024];
	char FileName_Problem_ptr[6];
	if (FileName_Problem[1] == 'c') {
		memcpy(FileName_Problem_ptr, &FileName_Problem[0], 5);
		FileName_Problem_ptr[5] = '\0';
	}
	else {
		memcpy(FileName_Problem_ptr, &FileName_Problem[0], 4);
		FileName_Problem_ptr[4] = '\0';
	}
	cout << FileName_Problem_ptr << endl;
	sprintf(filepath, "%s/%s", FilePath_Results_ptr, FileName_Problem_ptr);
	//string stringpath = filepath;
	status = mkdir(filepath);
	sprintf(filepath, "%s/%s/Subtours", FilePath_Results_ptr, FileName_Problem_ptr);
	status = mkdir(filepath);
	sprintf(filepath, "%s/%s/Subtours/%s_CurrentTours%d_SECIter%d.txt", FilePath_Results_ptr, FileName_Problem_ptr, FileName_Problem_ptr, loop_ptr, SECIterations);
	outfile.open(filepath);
	int TourCounter = 0;
	if (NonSub_ptr >= 0) {
		for (int l = 0; l < NonSub_ptr; l++) {
			TourCounter++;
			for (k = 0; k <= NodesInNonSubtour_ptr[l]; k++) {
				outfile << NonSubtoursNodes_ptr[l][k] << "\t" << XCOORD_i[NonSubtoursNodes_ptr[l][k]] << "\t" << YCOORD_i[NonSubtoursNodes_ptr[l][k]] << endl;
			}
			outfile << "NS" << TourCounter << "\t" << XCOORD_Center_Non_l[l] << "\t" << YCOORD_Center_Non_l[l] << endl;
		}
	}
	TourCounter = 0;
	if (Sub_ptr >= 0) {
		for (int l = 0; l < Sub_ptr; l++) {
			TourCounter++;
			for (k = 0; k <= NodesInSubtour_ptr[l]; k++) {
				outfile << SubtoursNodes_ptr[l][k] << "\t" << XCOORD_i[SubtoursNodes_ptr[l][k]] << "\t" << YCOORD_i[SubtoursNodes_ptr[l][k]] << endl;
			}
			outfile << "S" << TourCounter << "\t" << XCOORD_Center_l[l] << "\t" << YCOORD_Center_l[l] << "\t" << IsSubtourToBeEliminated_l[l] << endl;
		}
	}

	outfile.close();

	return 0;
}
int AddSECForMostDistant(IloEnv env, IloModel modelMaster_ptr, char* FilePath_Results_ptr, int Sub_ptr, int** SubtoursNodes_ptr, int* NodesInSubtour_ptr, int NonSub_ptr, int** NonSubtoursNodes_ptr, int* NodesInNonSubtour_ptr, IloNumVarMatrix5x5 X_ijkrm, int loop) {
	int status = 0;
	//Compute Coordinates of the Center of gravity for every subtour
	double* XCOORD_Center_l, * YCOORD_Center_l;//X,Y coordinates Center of gravity for every subtour
	XCOORD_Center_l = new double[Sub_ptr];
	YCOORD_Center_l = new double[Sub_ptr];
	for (int l = 0; l < Sub_ptr; l++) {
		XCOORD_Center_l[l] = 0;
		YCOORD_Center_l[l] = 0;
		for (k = 0; k < NodesInSubtour_ptr[l]; k++) {
			XCOORD_Center_l[l] += XCOORD_i[SubtoursNodes_ptr[l][k]];
			YCOORD_Center_l[l] += YCOORD_i[SubtoursNodes_ptr[l][k]];
		}
		XCOORD_Center_l[l] = XCOORD_Center_l[l] / NodesInSubtour_ptr[l];
		YCOORD_Center_l[l] = YCOORD_Center_l[l] / NodesInSubtour_ptr[l];
		//cout << XCOORD_Center_l[l] << '\t' << YCOORD_Center_l[l] << endl;
	}

	//Compute Coordinates of the Center of gravity for every Nonsubtour
	double* XCOORD_Center_Non_l, * YCOORD_Center_Non_l;//X,Y coordinates Center of gravity for every subtour
	XCOORD_Center_Non_l = new double[NonSub_ptr];
	YCOORD_Center_Non_l = new double[NonSub_ptr];
	if (NonSub_ptr > 0) {
		for (int l = 0; l < NonSub_ptr; l++) {
			XCOORD_Center_Non_l[l] = 0;
			YCOORD_Center_Non_l[l] = 0;
			for (k = 0; k < NodesInNonSubtour_ptr[l]; k++) {
				XCOORD_Center_Non_l[l] += XCOORD_i[NonSubtoursNodes_ptr[l][k]];
				YCOORD_Center_Non_l[l] += YCOORD_i[NonSubtoursNodes_ptr[l][k]];
			}
			XCOORD_Center_Non_l[l] = XCOORD_Center_Non_l[l] / NodesInNonSubtour_ptr[l];
			YCOORD_Center_Non_l[l] = YCOORD_Center_Non_l[l] / NodesInNonSubtour_ptr[l];
		}
	}



	//Compute the Distance between the Centers of gravity of every subtour

	double** Distance_Centers_lk;//Distance Matrix between i and j
	Distance_Centers_lk = new double* [Sub_ptr];
	for (int l = 0; l < Sub_ptr; l++) {
		Distance_Centers_lk[l] = new double[Sub_ptr + NonSub_ptr];
		for (k = 0; k < Sub_ptr + NonSub_ptr; k++) {
			Distance_Centers_lk[l][k] = 0;
		}
	}
	//cout << "Distances between the Centers of gravity of every subtour" << endl;
	for (int l = 0; l < Sub_ptr; l++) {
		for (k = 0; k < Sub_ptr + NonSub_ptr; k++) {
			if (k < Sub_ptr) {
				Distance_Centers_lk[l][k] = sqrt((XCOORD_Center_l[l] - XCOORD_Center_l[k]) * (XCOORD_Center_l[l] - XCOORD_Center_l[k]) + (YCOORD_Center_l[l] - YCOORD_Center_l[k]) * (YCOORD_Center_l[l] - YCOORD_Center_l[k]));
			}
			else if (NonSub_ptr > 0) {
				Distance_Centers_lk[l][k] = sqrt((XCOORD_Center_l[l] - XCOORD_Center_Non_l[k - Sub_ptr]) * (XCOORD_Center_l[l] - XCOORD_Center_Non_l[k - Sub_ptr]) + (YCOORD_Center_l[l] - YCOORD_Center_Non_l[k - Sub_ptr]) * (YCOORD_Center_l[l] - YCOORD_Center_Non_l[k - Sub_ptr]));
			}
			//cout << Distance_Centers_lk[l][k] << '\t';
		}
		//cout << std::endl;
	}

	//Compute the average distances between the Centers of gravity of every subtour
	//cout << "Average Distance of a Center of gravity from all the rest ones" << endl;
	double* Avg_Distance_Centers_l;
	Avg_Distance_Centers_l = new double[Sub_ptr];
	for (int l = 0; l < Sub_ptr; l++) {
		Avg_Distance_Centers_l[l] = 0;
	}
	for (int l = 0; l < Sub_ptr; l++) {
		for (k = 0; k < Sub_ptr + NonSub_ptr; k++) {
			Avg_Distance_Centers_l[l] += Distance_Centers_lk[l][k];
		}
		Avg_Distance_Centers_l[l] = Avg_Distance_Centers_l[l] / (Sub_ptr + NonSub_ptr - 1);
		//cout << Avg_Distance_Centers_l[l] << endl;
	}
	//Sort Subtours with Descending Avg_Distance_Centers_l
	double* Avg_Distance_Centers_SORTED_l;
	Avg_Distance_Centers_SORTED_l = new double[Sub_ptr];
	for (int l = 0; l < Sub_ptr; l++) {
		Avg_Distance_Centers_SORTED_l[l] = Avg_Distance_Centers_l[l];
	}
	double temp = 0;
	//cout << "BUBBLE SORT" << endl;
	//BUBBLE SORT
	for (int k = 0; k < Sub_ptr; k++) {
		for (int l = 0; l < Sub_ptr - 1; l++) {
			if (Avg_Distance_Centers_SORTED_l[l] < Avg_Distance_Centers_SORTED_l[l + 1]) {
				temp = Avg_Distance_Centers_SORTED_l[l];
				Avg_Distance_Centers_SORTED_l[l] = Avg_Distance_Centers_SORTED_l[l + 1];
				Avg_Distance_Centers_SORTED_l[l + 1] = temp;
			}
		}
	}

	/*for (int l = 0; l < Sub_ptr; l++) {
		cout << Avg_Distance_Centers_SORTED_l[l] << endl;
	}*/

	int NumberOfSECsToAdd = ceil(Sub_ptr / 2.0);// ADD ONLY HALF SUBTOUR ELIMINATION CONSTRAINTS;
	NumberOfSECsToAdd = Sub_ptr;// ADD ALL SUBTOUR ELIMINATION CONSTRAINTS;
	if (Sub_ptr == 1) NumberOfSECsToAdd = 1;
	//cout << "NumberOfSECsToAdd= " << NumberOfSECsToAdd << endl;
	double MinimumAverageDistanceToAdd = Avg_Distance_Centers_SORTED_l[NumberOfSECsToAdd - 1];
	//cout << "MinimumAverageDistanceToAdd= " << MinimumAverageDistanceToAdd << endl;

	//Determine which SECs will be added for which subtours
	int* IsSubtourToBeEliminated_l;
	IsSubtourToBeEliminated_l = new int[Sub_ptr];
	for (int l = 0; l < Sub_ptr; l++) {
		IsSubtourToBeEliminated_l[l] = 0;
	}
	int SECsAlreadyChosen = 0;
	//First, eliminate the subtour with the Max_Avg_Distance_Centers_SORTED_l
	if (Sub_ptr + NonSub_ptr > 1) {
		for (int l = 0; l < Sub_ptr; l++) {
			if (Avg_Distance_Centers_l[l] == Avg_Distance_Centers_SORTED_l[0]) {
				IsSubtourToBeEliminated_l[l] = 1;
				SECsAlreadyChosen++;
				//cout << "Subtour to be eliminated= " << l+1 << endl;
			}
		}
	}
	else {
		IsSubtourToBeEliminated_l[0] = 1;
		SECsAlreadyChosen++;
	}
	//Second, eliminate the subtour(s) with the Maximum distance from the already eliminated subtour(s)
	while (SECsAlreadyChosen < NumberOfSECsToAdd) {
		for (int l = 0; l < Sub_ptr; l++) {
			Avg_Distance_Centers_l[l] = 0;
		}
		for (int l = 0; l < Sub_ptr; l++) {
			if (IsSubtourToBeEliminated_l[l] == 1) {
				for (k = 0; k < Sub_ptr; k++) {
					Avg_Distance_Centers_l[k] += Distance_Centers_lk[l][k];
				}
				Avg_Distance_Centers_l[l] = 0;
			}
		}
		for (int l = 0; l < Sub_ptr; l++) {
			if (IsSubtourToBeEliminated_l[l] == 1) {
				Avg_Distance_Centers_l[l] = 0;
			}
			else {
				Avg_Distance_Centers_l[l] = Avg_Distance_Centers_l[l] / SECsAlreadyChosen;
			}
			Avg_Distance_Centers_SORTED_l[l] = Avg_Distance_Centers_l[l];
			//cout << Avg_Distance_Centers_l[l] << endl;
		}
		//BUBBLE SORT
		for (int k = 0; k < Sub_ptr; k++) {
			for (int l = 0; l < Sub_ptr - 1; l++) {
				if (Avg_Distance_Centers_SORTED_l[l] < Avg_Distance_Centers_SORTED_l[l + 1]) {
					temp = Avg_Distance_Centers_SORTED_l[l];
					Avg_Distance_Centers_SORTED_l[l] = Avg_Distance_Centers_SORTED_l[l + 1];
					Avg_Distance_Centers_SORTED_l[l + 1] = temp;
				}
			}
		}

		for (int l = 0; l < Sub_ptr; l++) {
			//cout << Avg_Distance_Centers_SORTED_l[l] << endl;
			if (Avg_Distance_Centers_l[l] == Avg_Distance_Centers_SORTED_l[0]) {
				IsSubtourToBeEliminated_l[l] = 1;
				SECsAlreadyChosen++;
				//cout << "Subtour to be eliminated= " << l + 1 << endl;
			}
		}
	}
	int startPrintLocal = clock();
	status = PrintCurrentTours(loop, FilePath_Results_ptr, Sub_ptr, SubtoursNodes_ptr, NodesInSubtour_ptr, NonSub_ptr, NonSubtoursNodes_ptr, NodesInNonSubtour_ptr, XCOORD_Center_l, YCOORD_Center_l, XCOORD_Center_Non_l, YCOORD_Center_Non_l, IsSubtourToBeEliminated_l);
	if (status != 0) {
		Found_Error("PrintCurrentTours");
		return -1;
	}
	int stopPrintLocal = clock();
	durationPrint = durationPrint + (long double)(stopPrintLocal - startPrintLocal) / CLOCKS_PER_SEC;
	status = CreateAddSECS(env, modelMaster_ptr, Sub_ptr, SubtoursNodes_ptr, NodesInSubtour_ptr, X_ijkrm, IsSubtourToBeEliminated_l, loop);
	if (status != 0) {
		Found_Error("CreateAddSECS");
		return -1;
	}


	return 0;
}
int Solve_Master(IloEnv env, IloModel modelMaster_ptr, IloCplex cplexMaster_ptr, IloNumVarMatrix5x5 X_ijkrm, IloNumVarMatrix3x3 Y_ikr, IloNumVarArray Heta_k, double* DTransposeY_ptr, bool* InfeasibleMaster = false) {

	cplexMaster_ptr.extract(modelMaster_ptr);
	//--------------SOLVE MASTER PROBLEM----------------	
	try {
		if (imax < 20) cplexMaster_ptr.exportModel("CurrentMaster.lp");
		cplexMaster_ptr.setOut(env.getNullStream());
		cplexMaster_ptr.setParam(IloCplex::EpGap, StopGapMaster);
		cplexMaster_ptr.setParam(IloCplex::TiLim, StopTime);
		//cplexMaster_ptr.solve();

		if (!cplexMaster_ptr.solve()) {
			env.error() << "Failed to optimize Master." << endl;
			env.out() << "----------------------------------------------------------------" << endl;
			*InfeasibleMaster = true;
			return 0;
		}

		env.out() << "Solution status Master = " << cplexMaster_ptr.getStatus() << endl;
		env.out() << "Solution value Master= " << cplexMaster_ptr.getObjValue() << endl;
		env.out() << "Optimality Gap= " << 100 * cplexMaster_ptr.getMIPRelativeGap() << "%" << endl;
		OptimalMasterObjFunction = cplexMaster_ptr.getObjValue();
		double GapMaster = cplexMaster_ptr.getMIPRelativeGap();

		//Gap = cplexMaster_ptr.getMIPRelativeGap();
		//SolutionStatus = cplexMaster_ptr.getStatus();

		for (k = 0; k < kmax; k++) {
			for (r = 0; r < rmax; r++) {
				for (i = 0; i < imax + 1; i++) {
					Y_ikrValue[i][k][r] = cplexMaster_ptr.getValue(Y_ikr[i][k][r]);
					if (Y_ikrValue[i][k][r] < 0.001) Y_ikrValue[i][k][r] = 0;
					//if (Y_ikrValue[i][k][r] != 0) cout << "Y_ikr[" << i << "][" << k << "][" << r << "]=" << Y_ikrValue[i][k][r] << endl;
					for (j = 0; j < jmax + 1; j++) {
						for (m = 0; m < mmax; m++) {
							X_ijkrmValue[i][j][k][r][m] = cplexMaster_ptr.getValue(X_ijkrm[i][j][k][r][m]);
							if (X_ijkrmValue[i][j][k][r][m] < 0.001) X_ijkrmValue[i][j][k][r][m] = 0;
							//if (X_ijkrmValue[i][j][k][r][m] != 0) cout << "X_ijkrm[" << i << "][" << j << "][" << k << "][" << r << "][" << m << "]=" << X_ijkrmValue[i][j][k][r][m] << endl;
						}
					}
				}
			}
		}


		//for (k = 0; k < kmax; k++) {
		//	for (r = 0; r < rmax; r++) {
		//		for (i = 0; i < imax + 1; i++) {
		//			for (j = 0; j < jmax + 1; j++) {
		//				for (m = 0; m < mmax; m++) {
		//					if (X_ijkrmValue[i][j][k][r][m] != 0) cout << "X_ijkrm[" << i << "][" << j << "][" << k << "][" << r << "][" << m << "]=" << X_ijkrmValue[i][j][k][r][m] << endl;
		//				}
		//			}
		//		}
		//	}
		//}

		//for (i = 0; i < imax + 1; i++) {
		//	for (k = 0; k < kmax; k++) {
		//		for (r = 0; r < rmax; r++) {
		//			//if (Y_jValue[j] < 0.001) Y_jValue[j] = 0;
		//			if (Y_ikrValue[i][k][r] != 0) cout << "Y_ikr[" << i << "][" << k << "][" << r << "]=" << Y_ikrValue[i][k][r] << endl;
		//		}
		//	}
		//}


		//for (k = 0; k < kmax; k++) {
		//	for (r = 0; r < rmax; r++) {
		//		for (i = 0; i < imax + 1; i++) {
		//			for (j = 0; j < jmax + 1; j++) {
		//				for (m = 0; m < mmax; m++) {
		//					Z_ijkrmValue[i][j][k][r][m] = cplexMaster_ptr.getValue(Z_ijkrm[i][j][k][r][m]);
		//					//if (X_ijValue[i][j] < 0.001) X_ijValue[i][j] = 0;
		//					//if (Z_ijkrmValue[i][j][k][r][m] != 0) cout << "Z_ijkrm[" << i << "][" << j << "][" << k << "][" << r << "][" << m << "]=" << Z_ijkrmValue[i][j][k][r][m] << endl;
		//				}
		//			}
		//		}
		//	}
		//}


		/*ofstream fsSolution;
		sprintf(filepath, "%s/%s/Combo=%s/SolutionBENDERS.txt", FilePath_Results_ptr, FileName_Problem, CombinationOfSlaveProblems_String);
		fsSolution.open(filepath);*/




		//cout << "Vehicle" << "	" << "Route" << "	" << "BreakPoint" << "	" << "From " << "	" << "To " << endl;//<< "	"<< "DepartureTime"
		//int test = 0;
		//double distance = 0;
		//for (k = 0; k < kmax; k++) {
		//	for (r = 0; r < rmax; r++) {
		//		for (m = 0; m < mmax; m++) {
		//			for (i = 0; i < 1; i++) {
		//				for (j = 1; j < jmax + 1; j++) {
		//					if (X_ijkrmValue[i][j][k][r][m] != 0) {
		//						test = j;
		//						//distance = distance + Distance_ij[i][j];
		//						cout << k << "	" << r << "	" << m << "	" << i << "	" << j << endl;//<< "	"<< ZZ_ikrValue[i][k][r]
		//						goto Restart;
		//					}
		//				}
		//			}
		//		}
		//	Restart:;
		//		for (m = 0; m < mmax; m++) {
		//			for (i = 0; i < imax; i++) {
		//				if (test != 0) {
		//					if (i == test) {
		//						for (j = 0; j < jmax + 1; j++) {
		//							if (X_ijkrmValue[i][j][k][r][m] != 0) {
		//								test = j;
		//								//distance = distance + Distance_ij[i][j];
		//								cout << k << "	" << r << "	" << m << "	" << i << "	" << j << endl;//<< "	"<< ZZ_ikrValue[i][k][r]
		//								if (test == jmax) {
		//									cout << k << "	" << r << "	" << m << "	" << i << "	" << j << endl;//<< "	"<< ZZ_ikrValue[imax][k][r]
		//								}
		//								i = 0;
		//								goto Restart;
		//							}
		//						}
		//					}
		//				}
		//				else break;
		//			}
		//		}
		//		cout << "-----------------------------------------------------	" << endl;
		//	}
		//}
		HetaValue = 0;
		/*fsSolution.close();*/
		for (k = 0; k < kmax; k++) {
			HetaValue = HetaValue + cplexMaster_ptr.getValue(Heta_k[k]);
			//if (HetaValue != 0) cout << "HetaValue=" << HetaValue << endl;
		}

		//--------LOWER BOUND------------
		double ExtraTerm = 0;
		/*for (k = 0; k < kmax; k++) {
			for (r = 0; r < rmax; r++) {
				for (j = 0; j < jmax + 1; j++) {
					for (m = 0; m < mmax; m++) {
						for (i = 0; i < imax + 1; i++) {
							ExtraTerm += g * TravelTimeMinimum_ijm[i][j][m] * X_ijkrmValue[i][j][k][r][m];
						}
					}
				}
			}
		}*/

		if (OptimalMasterObjFunction - OptimalMasterObjFunction * GapMaster > LowerBound) LowerBound = OptimalMasterObjFunction - OptimalMasterObjFunction * GapMaster;// -ExtraTerm;
		if (LowerBound > LowerBoundGlobal) LowerBoundGlobal = LowerBound;
		cout << "OptimalMasterObjFunction= " << OptimalMasterObjFunction << endl;
		//cout << "LowerBound= " << LowerBound << endl;//- ExtraTerm
		//cout << "LowerBoundGlobal= " << LowerBoundGlobal << endl;//- ExtraTerm
		//cout << "ExtraTerm= " << ExtraTerm << endl;
		*DTransposeY_ptr = OptimalMasterObjFunction - HetaValue;//- ExtraTerm
		//cout << "DTransposeY= " << *DTransposeY_ptr << endl;


		OptimalHetaValue = HetaValue;
		if (HetaValue > 0) cout << "HetaValue= " << HetaValue << endl;

	}
	catch (IloException& e) {
		cerr << "concert exception caught Master:" << e << endl;
	}
	catch (...) {
		cerr << "Unknown exception caught Master " << endl;
	}
	return 0;
}
//int Get_Slack_Values(IloCplex cplexMaster_ptr) {
//	//---------------Get SLACK values of the constraints of MASTER problem----------------
//
//	for (z = 0; z<zmax; z++) {
//		for (t = 0; t<tmax; t++) {
//			SlackValuesMasterCons = cplexMaster_ptr.getSlack(CT3Melzt[z][t]);
//			SlackValuesOfMainMasterCons.push_back(SlackValuesMasterCons);
//		}
//	}
//	for (i = 0; i<imax; i++) {
//		for (k = 0; k<kmax; k++) {
//			for (z = 0; z<zmax; z++) {
//				for (t = 0; t<tmax; t++) {
//					SlackValuesMasterCons = cplexMaster_ptr.getSlack(CT3C_ou_Dikzt[i][k][z][t]);
//					SlackValuesOfMainMasterCons.push_back(SlackValuesMasterCons);
//				}
//			}
//		}
//	}
//
//	for (z = 0; z<zmax; z++) {
//		for (j = 0; j<jmax; j++) {
//			SlackValuesMasterCons = cplexMaster_ptr.getSlack(SupFzj0[z][j]);
//			SlackValuesOfMainMasterCons.push_back(SlackValuesMasterCons);
//		}
//	}
//	for (i = 0; i<imax; i++) {
//		for (z = 0; z<zmax; z++) {
//			SlackValuesMasterCons = cplexMaster_ptr.getSlack(SupCiz0[i][z]);
//			SlackValuesOfMainMasterCons.push_back(SlackValuesMasterCons);
//		}
//	}
//	for (k = 0; k<kmax; k++) {
//		for (z = 0; z<zmax; z++) {
//			SlackValuesMasterCons = cplexMaster_ptr.getSlack(SupDkz0[k][z]);
//			SlackValuesOfMainMasterCons.push_back(SlackValuesMasterCons);
//		}
//	}
//	for (i = 0; i<imax; i++) {
//		for (t = 0; t<tmax; t++) {
//			SlackValuesMasterCons = cplexMaster_ptr.getSlack(Con3W1it[i][t]);
//			SlackValuesOfMainMasterCons.push_back(SlackValuesMasterCons);
//		}
//	}
//	for (k = 0; k<kmax; k++) {
//		for (t = 0; t<tmax; t++) {
//			SlackValuesMasterCons = cplexMaster_ptr.getSlack(Con5W2kt[k][t]);
//			SlackValuesOfMainMasterCons.push_back(SlackValuesMasterCons);
//		}
//	}
//	/*
//	IloRangeMatrix2x2 CT3Melzt(env,0);
//	IloRangeMatrix2x2 CT3C_ou_Dzt(env,0);
//	IloRangeMatrix2x2 SupFzj0(env,0);
//	IloRangeMatrix2x2 SupCiz0(env,0);
//	IloRangeMatrix2x2 SupDkz0(env,0);
//	IloRangeMatrix2x2 Con3W1it(env,0);
//	IloRangeMatrix2x2 Con5W2kt(env,0);
//	*/
//	//	cout<<"size of SLACK Array ="<<SlackValues.getSize()<<endl;
//
//	cplexMaster_ptr.getSlacks(SlackValues, BendersCuts);
//	//	cout<<"size of SLACK Array ="<<SlackValues.getSize()<<endl;
//
//	for (l = 0; l<SlackValues.getSize(); l++) {
//		/*
//		if(SlackValues[l]!=0){
//		cout<<"SlackValues["<<l<<"]="<<SlackValues[l]<<endl;
//		}
//		*/
//		SlackValuesOfBendersCuts.push_back(SlackValues[l]);
//	}
//	/*
//
//	for (l=0;l<SlackValuesOfBendersCuts.size();l++){
//
//	cout<<"SlackValuesOfBendersCuts["<<l<<"]="<<SlackValuesOfBendersCuts[l]<<endl;
//
//	}
//	*/
//	return 0;
//}
int UpdateSlaveRHS(IloRangeMatrix4x4 Con9_ZZZX_ijrm, IloRangeMatrix2x2 Con10a_ZZY_ir, IloRangeMatrix2x2 Con10b_ZZY_ir, IloRangeMatrix4x4 Con11a_ZX_ijrm, IloRangeMatrix4x4 Con11b_ZX_ijrm, IloRangeArray Con12_ZZY_n, IloRangeArray Con13_ZZY_r, IloRangeArray Con14_ZZY_r, int k) {
	//---------------Update the LB of the constraints of SLAVE problem----------------
	for (i = 0; i < imax + 1; i++) {
		for (j = 0; j < jmax + 1; j++) {
			for (r = 0; r < rmax; r++) {
				for (m = 0; m < mmax; m++) {
					X_ijrmValue[i][j][r][m] = X_ijkrmValue[i][j][k][r][m];
				}
			}
		}
	}
	for (i = 0; i < imax + 1; i++) {
		for (r = 0; r < rmax; r++) {
			for (m = 0; m < mmax; m++) {
				Y_irValue[i][r] = Y_ikrValue[i][k][r];
			}
		}
	}

	for (i = 0; i < imax; i++) {
		for (j = 1; j < jmax + 1; j++) {
			for (r = 0; r < rmax; r++) {
				for (m = 0; m < mmax; m++) {
					Con9_ZZZX_ijrm[i][j - 1][r][m].setLB(-((1 - X_ijrmValue[i][j][r][m]) * Big_M - zeta_ijm[i][j][m] - s_i[j]));
				}
			}
		}
	}
	for (i = 0; i < imax + 1; i++) {
		for (r = 0; r < rmax; r++) {
			Con10a_ZZY_ir[i][r].setLB((e_i[i] + s_i[i]) * Y_irValue[i][r]);
			Con10b_ZZY_ir[i][r].setLB(-(l_i[i] + s_i[i]) * Y_irValue[i][r]);
		}
	}

	/*for (i = 0; i < imax + 1; i++) {
		for (k = 0; k < kmax; k++) {
			for (r = 0; r < rmax; r++) {
				Con10b_ZZY_ikr[i][k][r].setUB((l_i[i] + s_i[i]) * Y_ikrValue[i][k][r]);
			}
		}
	}*/

	for (i = 0; i < imax + 1; i++) {
		for (j = 0; j < jmax + 1; j++) {
			for (r = 0; r < rmax; r++) {
				for (m = 0; m < mmax; m++) {
					Con11b_ZX_ijrm[i][j][r][m].setLB(-(w_ijm[i][j][m] * X_ijrmValue[i][j][r][m] + (1 - X_ijrmValue[i][j][r][m]) * Big_M));
					if (m > 0) {
						Con11a_ZX_ijrm[i][j][r][m - 1].setLB(w_ijm[i][j][m - 1] * X_ijrmValue[i][j][r][m] - (1 - X_ijrmValue[i][j][r][m]) * Big_M);
					}
				}
			}
		}
	}
	double Sum_lamda_s_Y_1;
	double Sum_lamda_s_Y_2;
	double Sum_lamda_s_Y_3;
	Sum_lamda_s_Y_1 = 0;
	for (i = 1; i < imax; i++) {
		Sum_lamda_s_Y_1 += lamda * s_i[i] * Y_irValue[i][0];
	}
	Con12_ZZY_n[0].setLB(Sum_lamda_s_Y_1);
	for (r = 0; r < rmax; r++) {
		if (r > 0) {
			Sum_lamda_s_Y_2 = 0;
			for (i = 1; i < imax; i++) {
				Sum_lamda_s_Y_2 += lamda * s_i[i] * Y_irValue[i][r];
			}
			Con13_ZZY_r[r - 1].setLB(Sum_lamda_s_Y_2);
		}
		Sum_lamda_s_Y_3 = 0;
		for (i = 1; i < imax; i++) {
			Sum_lamda_s_Y_3 -= lamda * s_i[i] * Y_irValue[i][r];
		}
		Sum_lamda_s_Y_3 += MaxTripDuration;
		Con14_ZZY_r[r].setLB(-Sum_lamda_s_Y_3);
	}



	return 0;
}
int UpdateAuxSlaveRHS(IloRangeArray Con2_aux_YX_n, IloRangeArray Con3_aux_YX_n, IloRangeArray Con4a_aux_YX_i, IloRangeArray Con4b_aux_YX_i, IloRangeMatrix3x3 Con9_aux_ZZZX_ijm, IloRangeArray Con10a_aux_ZZY_i, IloRangeArray Con10b_aux_ZZY_i, IloRangeMatrix3x3 Con11a_aux_ZX_ijm, IloRangeMatrix3x3 Con11b_aux_ZX_ijm, IloRangeArray Con14_aux_ZZY_n, int k_prime, int r_prime) {
	//---------------Update the LB of the constraints of SLAVE problem----------------
	for (i = 0; i < imax + 1; i++) {
		Y_iValue[i] = Y_ikrValue[i][k_prime][r_prime];
		//cout << "Y_iValue[" << i << "]=" << Y_iValue[i] << endl;
	}

	Con2_aux_YX_n[0].setLB(-IloInfinity);
	Con2_aux_YX_n[0].setUB(IloInfinity);
	Con2_aux_YX_n[0].setLB(Y_iValue[0]);
	Con2_aux_YX_n[0].setUB(Y_iValue[0]);

	Con3_aux_YX_n[0].setLB(-IloInfinity);
	Con3_aux_YX_n[0].setUB(IloInfinity);
	Con3_aux_YX_n[0].setLB(Y_iValue[imax]);
	Con3_aux_YX_n[0].setUB(Y_iValue[imax]);

	for (i = 1; i < imax; i++) {
		Con4a_aux_YX_i[i - 1].setLB(-IloInfinity);
		Con4a_aux_YX_i[i - 1].setUB(IloInfinity);
		Con4a_aux_YX_i[i - 1].setLB(Y_iValue[i]);
		Con4a_aux_YX_i[i - 1].setUB(Y_iValue[i]);
		Con4b_aux_YX_i[i - 1].setLB(-IloInfinity);
		Con4b_aux_YX_i[i - 1].setUB(IloInfinity);
		Con4b_aux_YX_i[i - 1].setLB(Y_iValue[i]);
		Con4b_aux_YX_i[i - 1].setUB(Y_iValue[i]);
	}

	for (i = 0; i < imax + 1; i++) {
		Con10a_aux_ZZY_i[i].setLB((e_i[i] + s_i[i]) * Y_iValue[i]);
		Con10b_aux_ZZY_i[i].setLB(-(l_i[i] + s_i[i]) * Y_iValue[i]);
	}

	double Sum_lamda_s_Y_3 = 0;
	for (i = 1; i < imax; i++) {
		Sum_lamda_s_Y_3 -= lamda * s_i[i] * Y_iValue[i];
	}
	Sum_lamda_s_Y_3 += MaxTripDuration;
	Con14_aux_ZZY_n[0].setLB(-Sum_lamda_s_Y_3);

	return 0;
}
int Solve_Slave(IloEnv env, IloModel modelSlave_ptr, IloCplex cplexSlave_ptr) {

	cplexSlave_ptr.extract(modelSlave_ptr);
	//-----------Solve Slave Problem--------------
	try {

		cplexSlave_ptr.setParam(IloCplex::PreInd, 0);
		cplexSlave_ptr.setParam(IloCplex::ScaInd, -1);
		cplexSlave_ptr.setParam(IloCplex::RootAlg, IloCplex::Dual);
		cplexSlave_ptr.exportModel("CurrentSlave.lp");
		cplexSlave_ptr.setOut(env.getNullStream());
		cplexSlave_ptr.solve();
		//env.out() << "Solution status of SLAVE problem = " << cplexSlave_ptr.getStatus() << endl;
		//env.out() << "Solution value of SLAVE problem = " << cplexSlave_ptr.getObjValue() << endl;


	}//end of try(try of primal slave 1)

	catch (IloException& e) {
		cerr << "concert exception caught:" << e << endl;
	}
	catch (...) {
		cerr << "Unknown exception caught" << endl;
	}
	return 0;
}
int Solve_AuxSlave(IloEnv env, IloModel modelAuxSlave, IloCplex cplexAuxSlave, IloNumVarMatrix3x3 X_aux_ijm, IloNumVarArray ZZ_aux_i, bool* InfeasibleAuxSlave = false) {

	cplexAuxSlave.extract(modelAuxSlave);
	//--------------SOLVE MASTER PROBLEM----------------	
	try {
		if (imax < 20) cplexAuxSlave.exportModel("CurrentAuxSlave.lp");
		cplexAuxSlave.setOut(env.getNullStream());
		//cplexAuxSlave.setParam(IloCplex::EpGap, StopGapMaster);
		cplexAuxSlave.setParam(IloCplex::TiLim, StopTimeAuxSlave);
		//cplexMaster_ptr.solve();

		int startAux = clock();
		if (!cplexAuxSlave.solve()) {
			int stopAux = clock();
			double durationAux = (long double)(stopAux - startAux) / CLOCKS_PER_SEC;
			if (durationAux < StopTimeAuxSlave - 1) {
				env.error() << "Failed to optimize Auxiliary Slave Problem." << endl;
				env.out() << "----------------------------------------------------------------" << endl;
				*InfeasibleAuxSlave = true;
				return 0;
			}
		}

		env.out() << "Solution status AuxSlave = " << cplexAuxSlave.getStatus() << endl;
		//env.out() << "Solution value AuxSlave= " << cplexAuxSlave.getObjValue() << endl;
		//env.out() << "Optimality Gap of AuxSlave= " << 100 * cplexAuxSlave.getMIPRelativeGap() << "%" << endl;
		//OptimalMasterObjFunction = cplexMaster_ptr.getObjValue();
		//GapAuxSlave = cplexAuxSlave.getMIPRelativeGap();

		//Gap = cplexMaster_ptr.getMIPRelativeGap();
		//SolutionStatus = cplexMaster_ptr.getStatus();

	}
	catch (IloException& e) {
		cerr << "concert exception caught Master:" << e << endl;
	}
	catch (...) {
		cerr << "Unknown exception caught Master " << endl;
	}

	//cout << "Vehicle" << "	" << "Route" << "	" << "BreakPoint" << "	" << "From " << "	" << "To " << endl;//<< "	"<< "DepartureTime"
	//	int test = 0;
	//	double distance = 0;
	//	//for (k = 0; k < kmax; k++) {
	//		//for (r = 0; r < rmax; r++) {
	//			for (m = 0; m < mmax; m++) {
	//				for (i = 0; i < 1; i++) {
	//					for (j = 1; j < jmax + 1; j++) {
	//						int g= cplexAuxSlave.getValue(X_aux_ijm[i][j][m]);
	//						if (g != 0) {
	//							test = j;
	//							//distance = distance + Distance_ij[i][j];
	//							cout  << m << "	" << i << "	" << j << endl;//<< "	"<< ZZ_ikrValue[i][k][r]
	//							goto Restart;
	//						}
	//					}
	//				}
	//			}
	//		Restart:;
	//			for (m = 0; m < mmax; m++) {
	//				for (i = 0; i < imax; i++) {
	//					if (test != 0) {
	//						if (i == test) {
	//							for (j = 0; j < jmax + 1; j++) {
	//								int g = cplexAuxSlave.getValue(X_aux_ijm[i][j][m]);
	//								if (g != 0) {
	//									test = j;
	//									//distance = distance + Distance_ij[i][j];
	//									cout <<  m << "	" << i << "	" << j << endl;//<< "	"<< ZZ_ikrValue[i][k][r]
	//									if (test == jmax) {
	//										cout << m << "	" << i << "	" << j << endl;//<< "	"<< ZZ_ikrValue[imax][k][r]
	//									}
	//									i = 0;
	//									goto Restart;
	//								}
	//							}
	//						}
	//					}
	//					else break;
	//				}
	//			}
	//			cout << "-----------------------------------------------------	" << endl;
	//		//}
	//	//}
	return 0;
}
int Slave_Infeasible(IloEnv env, int MultiSol) {
	//env.error() << "Failed to optimize Slave 1 LP PAME ALLI MIA THA TA KATAFERIS." << endl;
	//env.out() << "----------------------------------------------------------------" << endl;
	//------Upper Bound Global remains the same--------
	UpperBound = Big_M_bound;
	UpperBoundGlobal = UpperBoundGlobal;
	if (MultiSol == 0) UpperBoundOR = Big_M_bound;//The bound from the original master solution

	return 0;
}
int Slave_Feasible(IloEnv env, IloCplex cplexSlave_ptr, IloNumVarMatrix2x2 ZZ_ir, double* SlaveObjFunction, int k) {
	//env.error() << "Found a FEASIBLE solution of Slave LP" << endl;
	//env.out() << "----------------------------------------------------------------" << endl;
	SlaveObjFunction[k] = cplexSlave_ptr.getObjValue();
	for (r = 0; r < rmax; r++) {
		for (i = 0; i < imax + 1; i++) {
			ZZ_ikrValue[i][k][r] = cplexSlave_ptr.getValue(ZZ_ir[i][r]);
			//if (ZZ_ikrValue[i][k][r] != 0) cout << "ZZ_ikr[" << i << "][" << k << "][" << r << "]=" << ZZ_ikrValue[i][k][r] << endl;
		}
	}
	return 0;
}
int All_Slaves_Feasible(IloEnv env, IloCplex cplexSlave_ptr, double* DTransposeY, double* TotalSlaveObjFunction, double* SlaveObjFunction, int* NoOfRoutesUsed, int MultiSol) {
	//env.error() << "Found a FEASIBLE solution of Slave LP" << endl;
	//env.out() << "----------------------------------------------------------------" << endl;
	*TotalSlaveObjFunction = 0;
	for (k = 0; k < kmax; k++) {
		*TotalSlaveObjFunction = *TotalSlaveObjFunction + SlaveObjFunction[k];
	}
	UpperBound = *DTransposeY + *TotalSlaveObjFunction;
	if (MultiSol == 0)UpperBoundOR = *DTransposeY + *TotalSlaveObjFunction;
	SolutionStatus = 1;//Feasible
	*NoOfRoutesUsed = 0;
	for (k = 0; k < kmax; k++) {
		for (r = 0; r < rmax; r++) {
			if (Y_ikrValue[0][k][r] != 0) *NoOfRoutesUsed = *NoOfRoutesUsed + 1;
		}
	}


	if (UpperBound > UpperBoundGlobal) {//-----We found a worse feasible solution---
		UpperBoundGlobal = UpperBoundGlobal;
	}
	else {//-----------We found a better feasible solution-------
		UpperBoundGlobal = UpperBound;//Update Upper Bound
		OptimalOriginalObjFunction = UpperBoundGlobal;
		OptimalMasterObjFunction = *DTransposeY;
		OptimalSlaveObjFunction = *TotalSlaveObjFunction;
		for (k = 0; k < kmax; k++) {
			for (r = 0; r < rmax; r++) {
				for (i = 0; i < imax + 1; i++) {
					OptimalY_ikrValue[i][k][r] = Y_ikrValue[i][k][r];
					OptimalZZ_ikrValue[i][k][r] = ZZ_ikrValue[i][k][r];
					for (j = 0; j < jmax + 1; j++) {
						for (m = 0; m < mmax; m++) {
							OptimalX_ijkrmValue[i][j][k][r][m] = X_ijkrmValue[i][j][k][r][m];
						}
					}
				}
			}
		}

		OptimalHetaValue = HetaValue;

	}//end of else (better feasible solution found)

	cTx.push_back(*TotalSlaveObjFunction);


	return 0;
}
int Generate_Feasible_Solution(bool* NewSolution) {
	//cout << "-GENERATE A FEASIBLE SOLUTION-" << endl;
	int Current_Sol = 0;
	bool NodesInOrder = false;
	while (NodesInOrder == false) {
	StartOver:;
		NodesInOrder = true;
		for (k = 0; k < kmax; k++) {
			for (r = 0; r < rmax; r++) {
				for (int m_i = 0; m_i < mmax; m_i++) {
					for (int m_l = 0; m_l < mmax; m_l++) {
						for (i = 0; i < imax; i++) {
							for (j = 0; j < jmax; j++) {
								for (int l = 0; l < jmax + 1; l++) {
									if (X_ijkrmValue[i][l][k][r][m_i] == 1 && X_ijkrmValue[l][j][k][r][m_l] == 1 && e_i[j] < e_i[l]) {
										NodesInOrder = false;
										*NewSolution = true;
										X_ijkrmValue[i][j][k][r][m_i] = 1;
										X_ijkrmValue[j][l][k][r][m_l] = 1;
										X_ijkrmValue[i][l][k][r][m_i] = 0;
										X_ijkrmValue[l][j][k][r][m_l] = 0;
										bool FoundNextNode = false;
										for (int m_j = 0; m_j < mmax; m_j++) {
											for (i = 1; i < imax + 1; i++) {
												if (X_ijkrmValue[j][i][k][r][m_j] != 0 && i != l) {
													X_ijkrmValue[j][i][k][r][m_j] = 0;
													if (m_j > 0) {
														if (w_ijm[i][j][m_j - 1] < l_i[l] + s_i[l] || w_ijm[i][j][m_j] > e_i[l] + s_i[l]) {
															X_ijkrmValue[l][i][k][r][m_j] = 1;
														}
														else {
															X_ijkrmValue[l][i][k][r][m_l] = 1;
														}
													}
													else {
														if (w_ijm[i][j][m_j] > e_i[l] + s_i[l]) {
															X_ijkrmValue[l][i][k][r][m_j] = 1;
														}
														else {
															X_ijkrmValue[l][i][k][r][m_l] = 1;
														}

													}
													FoundNextNode = true;
													goto StartOver;
												}
											}
										}
										if (FoundNextNode == false) {
											cout << "Could not find the next node" << endl;
											cout << "i= " << i << endl;
											cout << "l= " << l << endl;
											cout << "j= " << j << endl;
											goto NewSolution;
										}
									}
								}
							}
						}
					}
				}
			}
		}
	}

NewSolution:;

	for (k = 0; k < kmax; k++) {
		for (r = 0; r < rmax; r++) {
			for (i = 0; i < imax; i++) {
				for (j = 1; j < jmax + 1; j++) {
					for (m = 0; m < mmax; m++) {
						if (X_ijkrmValue[i][j][k][r][m] != 0) {
							if (DualValueCon11a_ZX_ijkrm[i][j][k][r][m] != 0) {
								if (w_ijm[i][j][m - 1] > e_i[i] + s_i[i]) {
									X_ijkrmValue[i][j][k][r][m] = 0;
									X_ijkrmValue[i][j][k][r][m - 1] = 1;
								}
							}
							if (DualValueCon11b_ZX_ijkrm[i][j][k][r][m] != 0) {
								if (w_ijm[i][j][m] < l_i[i] + s_i[i]) {
									X_ijkrmValue[i][j][k][r][m] = 0;
									X_ijkrmValue[i][j][k][r][m + 1] = 1;
								}
							}
						}
					}
				}
			}
			if (DualValueCon14_ZZY_kr[k][r] != 0) {
				for (j = 1; j < jmax + 1; j++) {
					for (m = 0; m < mmax; m++) {
						if (X_ijkrmValue[0][j][k][r][m] != 0) {
							X_ijkrmValue[0][j][k][r][m] = 0;
							X_ijkrmValue[0][j][k][r][m + 1] = 1;
							goto ShowSolution;
						}
					}
				}
			}
		}
	}
ShowSolution:;
	//cout << "Vehicle" << "	" << "Route" << "	" << "BreakPoint" << "	" << "From " << "	" << "To " << endl;//<< "	"<< "DepartureTime"
	//int test = 0;
	//double distance = 0;
	//for (k = 0; k < kmax; k++) {
	//	for (r = 0; r < rmax; r++) {
	//		for (m = 0; m < mmax; m++) {
	//			for (i = 0; i < 1; i++) {
	//				for (j = 1; j < jmax + 1; j++) {
	//					if (X_ijkrmValue[i][j][k][r][m] != 0) {
	//						test = j;
	//						//distance = distance + Distance_ij[i][j];
	//						cout << k << "	" << r << "	" << m << "	" << i << "	" << j << endl;//<< "	"<< ZZ_ikrValue[i][k][r]
	//						goto Restart;
	//					}
	//				}
	//			}
	//		}
	//	Restart:;
	//		for (m = 0; m < mmax; m++) {
	//			for (i = 0; i < imax; i++) {
	//				if (test != 0) {
	//					if (i == test) {
	//						for (j = 0; j < jmax + 1; j++) {
	//							if (X_ijkrmValue[i][j][k][r][m] != 0) {
	//								test = j;
	//								//distance = distance + Distance_ij[i][j];
	//								cout << k << "	" << r << "	" << m << "	" << i << "	" << j << endl;//<< "	"<< ZZ_ikrValue[i][k][r]
	//								if (test == jmax) {
	//									cout << k << "	" << r << "	" << m << "	" << i << "	" << j << endl;//<< "	"<< ZZ_ikrValue[imax][k][r]
	//								}
	//								i = 0;
	//								goto Restart;
	//							}
	//						}
	//					}
	//				}
	//				else break;
	//			}
	//		}
	//		cout << "-----------------------------------------------------	" << endl;
	//	}
	//}
	/*for (k = 0; k < kmax; k++) {
		for (r = 0; r < rmax; r++) {
			for (m = 0; m < mmax; m++) {
				for (i = 0; i < imax+1; i++) {
					for (j = 0; j < jmax + 1; j++) {
						if (X_ijkrmValue[i][j][k][r][m] != 0) cout << "X_ijkrm[" << i << "][" << j << "][" << k << "][" << r << "][" << m << "]=" << X_ijkrmValue[i][j][k][r][m] << endl;
					}
				}
			}
		}
	}*/
	return 0;
}
int Generate_Multiple_Solutions(int MultiSol, bool* GeneratedNewSolution, int* NodeChanged, int k_ptr) {
	//cout << "-GENERATE MULTIPLE SOLUTIONS-" << endl;
	int Current_Sol = 0;
	bool FoundDualValueCon9 = false;

	int l_ptr = 0, test = 0;
	int* NodesInInfeasibleTour;
	NodesInInfeasibleTour = new int[imax];
	for (r = 0; r < rmax; r++) {
		for (m = 0; m < mmax; m++) {
			for (j = 1; j < jmax + 1; j++) {
				if (X_ijkrmValue[0][j][k_ptr][r][m] != 0) {
					test = j;
					//distance = distance + Distance_ij[i][j];
					//cout << k << "	" << r << "	" << m << "	" << i << "	" << j << endl;//<< "	"<< ZZ_ikrValue[i][k_ptr][r]
					goto StartAgain;
				}
			}
		}
	StartAgain:;
		for (m = 0; m < mmax; m++) {
			for (i = 0; i < imax; i++) {
				if (test != 0) {
					if (i == test) {
						for (j = 0; j < jmax + 1; j++) {
							if (X_ijkrmValue[i][j][k_ptr][r][m] != 0) {
								if (DualValueCon9_ZZZX_ijkrm[i][j][k_ptr][r][m] != 0) {
									NodesInInfeasibleTour[l_ptr] = i;
									//cout << NodesInInfeasibleTour[l_ptr] << endl;//<< "	"<< ZZ_ikrValue[imax][k_ptr][r]
									l_ptr++;
									//goto Finish;
								}
								test = j;
								//distance = distance + Distance_ij[i][j];
								//cout << k << "	" << r << "	" << m << "	" << i << "	" << j << endl;//<< "	"<< ZZ_ikrValue[i][k_ptr][r]
								if (test == jmax) {
									//cout << k << "	" << r << "	" << m << "	" << i << "	" << j << endl;//<< "	"<< ZZ_ikrValue[imax][k_ptr][r]
								}
								i = 0;
								goto StartAgain;
							}
						}
					}
				}
				else break;
			}

		}
		//cout << "-----------------------------------------------------	" << endl;
	}

Finish:;
	//cout << "l_ptr=	"<<l_ptr << endl;






	//bool NodesInOrder = false;
	//while (NodesInOrder == false) {
StartOver:;
	//NodesInOrder = true;
	//for (k = 0; k < kmax; k++) {
	for (r = 0; r < rmax; r++) {
		for (int m_l = 0; m_l < mmax; m_l++) {
			for (int l = 0; l < l_ptr; l++) {
				for (j = 0; j < jmax; j++) {
					if (DualValueCon9_ZZZX_ijkrm[NodesInInfeasibleTour[l]][j][k_ptr][r][m_l] != 0) {
						for (i = 0; i < imax; i++) {
							for (int m_i = 0; m_i < mmax; m_i++) {
								if (m_l > 0) {
									if (X_ijkrmValue[i][NodesInInfeasibleTour[l]][k_ptr][r][m_i] != 0 && X_ijkrmValue[NodesInInfeasibleTour[l]][j][k_ptr][r][m_l] != 0 && (w_ijm[j][NodesInInfeasibleTour[l]][m_l - 1] < l_i[j] + s_i[j] && w_ijm[j][NodesInInfeasibleTour[l]][m_l] > e_i[j] + s_i[j]) && e_i[j] + s_i[j] + TravelTimeMinimum_ijm[j][NodesInInfeasibleTour[l]][m_l] < l_i[NodesInInfeasibleTour[l]]) {//if  {//e_i[j] < e_i[NodesInInfeasibleTour[l]]
										FoundDualValueCon9 = true;

										Current_Sol++;
										if (j != *NodeChanged) {
											//NodesInOrder = false;
//*NewSolution = true;
											*NodeChanged = NodesInInfeasibleTour[l];
											X_ijkrmValue[i][j][k_ptr][r][m_i] = 1;
											X_ijkrmValue[j][NodesInInfeasibleTour[l]][k_ptr][r][m_l] = 1;
											X_ijkrmValue[i][NodesInInfeasibleTour[l]][k_ptr][r][m_i] = 0;
											X_ijkrmValue[NodesInInfeasibleTour[l]][j][k_ptr][r][m_l] = 0;
											bool FoundNextNode = false;
											*GeneratedNewSolution = true;
											for (int m_j = 0; m_j < mmax; m_j++) {
												for (i = 1; i < imax + 1; i++) {
													if (X_ijkrmValue[j][i][k_ptr][r][m_j] != 0 && i != NodesInInfeasibleTour[l]) {
														X_ijkrmValue[j][i][k_ptr][r][m_j] = 0;
														if (m_j > 0) {
															if (w_ijm[NodesInInfeasibleTour[l]][i][m_j - 1] < l_i[NodesInInfeasibleTour[l]] + s_i[NodesInInfeasibleTour[l]] && w_ijm[NodesInInfeasibleTour[l]][i][m_j] > e_i[NodesInInfeasibleTour[l]] + s_i[NodesInInfeasibleTour[l]]) {
																X_ijkrmValue[NodesInInfeasibleTour[l]][i][k_ptr][r][m_j] = 1;
															}
															else {
																X_ijkrmValue[NodesInInfeasibleTour[l]][i][k_ptr][r][m_l] = 1;
															}
														}
														else {
															if (w_ijm[NodesInInfeasibleTour[l]][i][m_j] > e_i[NodesInInfeasibleTour[l]] + s_i[NodesInInfeasibleTour[l]]) {
																X_ijkrmValue[NodesInInfeasibleTour[l]][i][k_ptr][r][m_j] = 1;
															}
															else {
																X_ijkrmValue[NodesInInfeasibleTour[l]][i][k_ptr][r][m_l] = 1;
															}

														}
														FoundNextNode = true;
														goto NewSolution;
													}
												}
											}
											if (FoundNextNode == false) {
												cout << "Could not find the next node" << endl;
												cout << "i= " << i << endl;
												cout << "l= " << l << endl;
												cout << "j= " << j << endl;
												goto NewSolution;
											}
										}
									}
								}
								else {
									if (X_ijkrmValue[i][NodesInInfeasibleTour[l]][k_ptr][r][m_i] != 0 && X_ijkrmValue[NodesInInfeasibleTour[l]][j][k_ptr][r][m_l] != 0 && (w_ijm[j][NodesInInfeasibleTour[l]][m_l] > e_i[j] + s_i[j]) && e_i[j] + s_i[j] + TravelTimeMinimum_ijm[j][NodesInInfeasibleTour[l]][m_l] < l_i[NodesInInfeasibleTour[l]]) {//if  {//e_i[j] < e_i[NodesInInfeasibleTour[l]]
										Current_Sol++;
										//NodesInOrder = false;
										//*NewSolution = true;
										if (j != *NodeChanged) {
											*NodeChanged = NodesInInfeasibleTour[l];
											X_ijkrmValue[i][j][k_ptr][r][m_i] = 1;
											X_ijkrmValue[j][NodesInInfeasibleTour[l]][k_ptr][r][m_l] = 1;
											X_ijkrmValue[i][NodesInInfeasibleTour[l]][k_ptr][r][m_i] = 0;
											X_ijkrmValue[NodesInInfeasibleTour[l]][j][k_ptr][r][m_l] = 0;
											bool FoundNextNode = false;
											*GeneratedNewSolution = true;
											for (int m_j = 0; m_j < mmax; m_j++) {
												for (i = 1; i < imax + 1; i++) {
													if (X_ijkrmValue[j][i][k_ptr][r][m_j] != 0 && i != NodesInInfeasibleTour[l]) {
														X_ijkrmValue[j][i][k_ptr][r][m_j] = 0;
														if (m_j > 0) {
															if (w_ijm[NodesInInfeasibleTour[l]][i][m_j - 1] < l_i[NodesInInfeasibleTour[l]] + s_i[NodesInInfeasibleTour[l]] && w_ijm[NodesInInfeasibleTour[l]][i][m_j] > e_i[NodesInInfeasibleTour[l]] + s_i[NodesInInfeasibleTour[l]]) {
																X_ijkrmValue[NodesInInfeasibleTour[l]][i][k_ptr][r][m_j] = 1;
															}
															else {
																X_ijkrmValue[NodesInInfeasibleTour[l]][i][k_ptr][r][m_l] = 1;
															}
														}
														else {
															if (w_ijm[NodesInInfeasibleTour[l]][i][m_j] > e_i[NodesInInfeasibleTour[l]] + s_i[NodesInInfeasibleTour[l]]) {
																X_ijkrmValue[NodesInInfeasibleTour[l]][i][k_ptr][r][m_j] = 1;
															}
															else {
																X_ijkrmValue[NodesInInfeasibleTour[l]][i][k_ptr][r][m_l] = 1;
															}

														}
														FoundNextNode = true;
														goto NewSolution;
													}
												}
											}
											if (FoundNextNode == false) {
												cout << "Could not find the next node" << endl;
												cout << "i= " << i << endl;
												cout << "l= " << l << endl;
												cout << "j= " << j << endl;
												goto NewSolution;
											}
										}
									}

								}

							}
						}
					}
					//}
				}
			}
		}
	}
	//}
//}







	//SHOULD WE DELETE IT???
	if (FoundDualValueCon9 == false) {
		for (r = 0; r < rmax; r++) {
			for (int m_i = 0; m_i < mmax; m_i++) {
				for (int m_l = 0; m_l < mmax; m_l++) {
					for (i = 0; i < imax; i++) {
						for (j = 0; j < jmax; j++) {
							for (int l = 0; l < jmax + 1; l++) {

								if (m_l > 0) {
									if (X_ijkrmValue[i][l][k_ptr][r][m_i] != 0 && X_ijkrmValue[l][j][k_ptr][r][m_l] != 0 && (w_ijm[j][l][m_l - 1] < l_i[j] + s_i[j] && w_ijm[j][l][m_l] > e_i[j] + s_i[j]) && e_i[j] + s_i[j] + TravelTimeMinimum_ijm[j][l][m_l] < l_i[l]) {//if  {//e_i[j] < e_i[l]
										Current_Sol++;
										if (j != *NodeChanged) {
											//NodesInOrder = false;
//*NewSolution = true;
											*NodeChanged = NodesInInfeasibleTour[l];
											X_ijkrmValue[i][j][k_ptr][r][m_i] = 1;
											X_ijkrmValue[j][l][k_ptr][r][m_l] = 1;
											X_ijkrmValue[i][l][k_ptr][r][m_i] = 0;
											X_ijkrmValue[l][j][k_ptr][r][m_l] = 0;
											bool FoundNextNode = false;
											*GeneratedNewSolution = true;
											for (int m_j = 0; m_j < mmax; m_j++) {
												for (i = 1; i < imax + 1; i++) {
													if (X_ijkrmValue[j][i][k_ptr][r][m_j] != 0 && i != l) {
														X_ijkrmValue[j][i][k_ptr][r][m_j] = 0;
														if (m_j > 0) {
															if (w_ijm[l][i][m_j - 1] < l_i[l] + s_i[l] && w_ijm[l][i][m_j] > e_i[l] + s_i[l]) {
																X_ijkrmValue[l][i][k_ptr][r][m_j] = 1;
															}
															else {
																X_ijkrmValue[l][i][k_ptr][r][m_l] = 1;
															}
														}
														else {
															if (w_ijm[l][i][m_j] > e_i[l] + s_i[l]) {
																X_ijkrmValue[l][i][k_ptr][r][m_j] = 1;
															}
															else {
																X_ijkrmValue[l][i][k_ptr][r][m_l] = 1;
															}

														}
														FoundNextNode = true;
														goto NewSolution;
													}
												}
											}
											if (FoundNextNode == false) {
												cout << "Could not find the next node" << endl;
												cout << "i= " << i << endl;
												cout << "l= " << l << endl;
												cout << "j= " << j << endl;
												goto NewSolution;
											}
										}
									}
								}
								else {
									if (X_ijkrmValue[i][l][k_ptr][r][m_i] != 0 && X_ijkrmValue[l][j][k_ptr][r][m_l] != 0 && (w_ijm[j][l][m_l] > e_i[j] + s_i[j]) && e_i[j] + s_i[j] + TravelTimeMinimum_ijm[j][l][m_l] < l_i[l]) {//if  {//e_i[j] < e_i[l]
										Current_Sol++;
										//NodesInOrder = false;
										//*NewSolution = true;
										if (j != *NodeChanged) {
											*NodeChanged = NodesInInfeasibleTour[l];
											X_ijkrmValue[i][j][k_ptr][r][m_i] = 1;
											X_ijkrmValue[j][l][k_ptr][r][m_l] = 1;
											X_ijkrmValue[i][l][k_ptr][r][m_i] = 0;
											X_ijkrmValue[l][j][k_ptr][r][m_l] = 0;
											bool FoundNextNode = false;
											*GeneratedNewSolution = true;
											for (int m_j = 0; m_j < mmax; m_j++) {
												for (i = 1; i < imax + 1; i++) {
													if (X_ijkrmValue[j][i][k_ptr][r][m_j] != 0 && i != l) {
														X_ijkrmValue[j][i][k_ptr][r][m_j] = 0;
														if (m_j > 0) {
															if (w_ijm[l][i][m_j - 1] < l_i[l] + s_i[l] && w_ijm[l][i][m_j] > e_i[l] + s_i[l]) {
																X_ijkrmValue[l][i][k_ptr][r][m_j] = 1;
															}
															else {
																X_ijkrmValue[l][i][k_ptr][r][m_l] = 1;
															}
														}
														else {
															if (w_ijm[l][i][m_j] > e_i[l] + s_i[l]) {
																X_ijkrmValue[l][i][k_ptr][r][m_j] = 1;
															}
															else {
																X_ijkrmValue[l][i][k_ptr][r][m_l] = 1;
															}

														}
														FoundNextNode = true;
														goto NewSolution;
													}
												}
											}
											if (FoundNextNode == false) {
												cout << "Could not find the next node" << endl;
												cout << "i= " << i << endl;
												cout << "l= " << l << endl;
												cout << "j= " << j << endl;
												goto NewSolution;
											}
										}
									}

								}

							}
						}
					}
				}
			}
		}
	}

NewSolution:;

	//for (k = 0; k < kmax; k++) {
	for (r = 0; r < rmax; r++) {
		for (i = 0; i < imax; i++) {
			for (j = 1; j < jmax + 1; j++) {
				for (m = 0; m < mmax; m++) {
					if (X_ijkrmValue[i][j][k_ptr][r][m] != 0) {
						if (DualValueCon11a_ZX_ijkrm[i][j][k_ptr][r][m] != 0) {
							if (w_ijm[i][j][m - 1] > e_i[i] + s_i[i]) {
								X_ijkrmValue[i][j][k_ptr][r][m] = 0;
								X_ijkrmValue[i][j][k_ptr][r][m - 1] = 1;
							}
						}
						if (DualValueCon11b_ZX_ijkrm[i][j][k_ptr][r][m] != 0) {
							if (w_ijm[i][j][m] < l_i[i] + s_i[i]) {
								X_ijkrmValue[i][j][k_ptr][r][m] = 0;
								X_ijkrmValue[i][j][k_ptr][r][m + 1] = 1;
							}
						}
					}
				}
			}
		}
		if (DualValueCon14_ZZY_kr[k_ptr][r] != 0) {
			for (j = 1; j < jmax + 1; j++) {
				for (m = 0; m < mmax; m++) {
					if (X_ijkrmValue[0][j][k_ptr][r][m] != 0) {
						int m_zero = m;
						int m_next;
						for (i = 1; i < imax + 1; i++) {
							for (int m_prime = 0; m_prime < mmax; m_prime++) {
								if (X_ijkrmValue[j][i][k_ptr][r][m_prime] != 0) m_next = m_prime;
							}
						}
						if (m_zero < m_next) {
							X_ijkrmValue[0][j][k_ptr][r][m] = 0;
							X_ijkrmValue[0][j][k_ptr][r][m + 1] = 1;
							goto ShowSolution;
						}

					}
				}
			}
		}
	}
	//}
ShowSolution:;
	//cout << "Vehicle" << "	" << "Route" << "	" << "BreakPoint" << "	" << "From " << "	" << "To " << endl;//<< "	"<< "DepartureTime"
	//double distance = 0;
	////for (k = 0; k < kmax; k++) {
	//for (r = 0; r < rmax; r++) {
	//	for (m = 0; m < mmax; m++) {
	//		for (i = 0; i < 1; i++) {
	//			for (j = 1; j < jmax + 1; j++) {
	//				if (X_ijkrmValue[i][j][k_ptr][r][m] != 0) {
	//					test = j;
	//					//distance = distance + Distance_ij[i][j];
	//					cout << k << "	" << r << "	" << m << "	" << i << "	" << j << endl;//<< "	"<< ZZ_ikrValue[i][k_ptr][r]
	//					goto Restart;
	//				}
	//			}
	//		}
	//	}
	//Restart:;
	//	for (m = 0; m < mmax; m++) {
	//		for (i = 0; i < imax; i++) {
	//			if (test != 0) {
	//				if (i == test) {
	//					for (j = 0; j < jmax + 1; j++) {
	//						if (X_ijkrmValue[i][j][k_ptr][r][m] != 0) {
	//							test = j;
	//							//distance = distance + Distance_ij[i][j];
	//							cout << k << "	" << r << "	" << m << "	" << i << "	" << j << endl;//<< "	"<< ZZ_ikrValue[i][k_ptr][r]
	//							if (test == jmax) {
	//								cout << k << "	" << r << "	" << m << "	" << i << "	" << j << endl;//<< "	"<< ZZ_ikrValue[imax][k_ptr][r]
	//							}
	//							i = 0;
	//							goto Restart;
	//						}
	//					}
	//				}
	//			}
	//			else break;
	//		}
	//	}
	//	cout << "-----------------------------------------------------	" << endl;
	//}
	//}
	/*for (k = 0; k < kmax; k++) {
		for (r = 0; r < rmax; r++) {
			for (m = 0; m < mmax; m++) {
				for (i = 0; i < imax+1; i++) {
					for (j = 0; j < jmax + 1; j++) {
						if (X_ijkrmValue[i][j][k_ptr][r][m] != 0) cout << "X_ijkrm[" << i << "][" << j << "][" << k << "][" << r << "][" << m << "]=" << X_ijkrmValue[i][j][k_ptr][r][m] << endl;
					}
				}
			}
		}
	}*/
	return 0;
}
int GetExtremeRayOfDSP(IloCplex cplexSlave_ptr, IloNumArray FeasDualValues, IloRangeMatrix4x4 Con9_ZZZX_ijrm, int k) {
	//----------------Get an extreme ray of the DUAL SLAVE problem-------------
	//cout << "size of Array =" << FeasDualValues.getSize() << endl;
	cplexSlave_ptr.dualFarkas(Con9_ZZZX_ijrm[0][0][0], FeasDualValues);
	//cout << "size of Array =" << FeasDualValues.getSize() << endl;
	int l;
	/*for (l = 0; l < FeasDualValues.getSize(); l++) {
		if (FeasDualValues[l] != 0) {
			cout << "FeasDualValues[" << l << "]=" << FeasDualValues[l] << endl;
		}
	}*/

	//cout << "ETREME RAY:" << endl;
	l = 0;
	for (i = 0; i < imax; i++) {
		for (j = 1; j < jmax + 1; j++) {
			for (r = 0; r < rmax; r++) {
				for (m = 0; m < mmax; m++) {
					DualValueCon9_ZZZX_ijkrm[i][j][k][r][m] = FeasDualValues[l];
					//if (DualValueCon9_ZZZX_ijkrm[i][j][k][r][m] != 0)cout << "DualValueCon9_ZZZX_ijkrm[" << i << "][" << j << "][" << k << "][" << r << "][" << m << "]=" << DualValueCon9_ZZZX_ijkrm[i][j][k][r][m] << endl;
					l++;
				}
			}
		}
	}
	for (i = 0; i < imax + 1; i++) {
		for (r = 0; r < rmax; r++) {
			DualValueCon10a_ZZY_ikr[i][k][r] = FeasDualValues[l];
			//if (DualValueCon10a_ZZY_ikr[i][k][r] != 0)cout << "DualValueCon10a_ZZY_ikr[" << i << "][" << k << "][" << r << "]=" << DualValueCon10a_ZZY_ikr[i][k][r] << endl;
			l++;
		}
	}

	for (i = 0; i < imax + 1; i++) {
		for (r = 0; r < rmax; r++) {
			DualValueCon10b_ZZY_ikr[i][k][r] = FeasDualValues[l];
			//if (DualValueCon10b_ZZY_ikr[i][k][r] != 0)cout << "DualValueCon10b_ZZY_ikr[" << i << "][" << k << "][" << r << "]=" << DualValueCon10b_ZZY_ikr[i][k][r] << endl;
			l++;
		}
	}

	for (i = 0; i < imax + 1; i++) {
		for (j = 0; j < jmax + 1; j++) {
			for (r = 0; r < rmax; r++) {
				for (m = 1; m < mmax; m++) {
					DualValueCon11a_ZX_ijkrm[i][j][k][r][m] = FeasDualValues[l];
					//if (DualValueCon11a_ZX_ijkrm[i][j][k][r][m] != 0)cout << "DualValueCon11a_ZX_ijkrm[" << i << "][" << j << "][" << k << "][" << r << "][" << m << "]=" << DualValueCon11a_ZX_ijkrm[i][j][k][r][m] << endl;
					l++;
				}
			}
		}
	}


	for (i = 0; i < imax + 1; i++) {
		for (j = 0; j < jmax + 1; j++) {
			for (r = 0; r < rmax; r++) {
				for (m = 0; m < mmax; m++) {
					DualValueCon11b_ZX_ijkrm[i][j][k][r][m] = FeasDualValues[l];
					//if (DualValueCon11b_ZX_ijkrm[i][j][k][r][m] != 0)cout << "DualValueCon11b_ZX_ijkrm[" << i << "][" << j << "][" << k << "][" << r << "][" << m << "]=" << DualValueCon11b_ZX_ijkrm[i][j][k][r][m] << endl;
					l++;
				}
			}
		}
	}
	DualValueCon12_ZZY_k[k] = FeasDualValues[l];
	//if (DualValueCon12_ZZY_k[k] != 0)cout << "DualValueCon12_ZZY_k[" << k << "]=" << DualValueCon12_ZZY_k[k] << endl;
	l++;
	for (r = 1; r < rmax; r++) {
		DualValueCon13_ZZY_kr[k][r] = FeasDualValues[l];
		//if (DualValueCon13_ZZY_kr[k][r] != 0)cout << "DualValueCon13_ZZY_kr[" << k << "][" << r << "]=" << DualValueCon13_ZZY_kr[k][r] << endl;
		l++;
	}
	for (r = 0; r < rmax; r++) {
		DualValueCon14_ZZY_kr[k][r] = FeasDualValues[l];
		//if (DualValueCon14_ZZY_kr[k][r] != 0)cout << "DualValueCon14_ZZY_kr[" << k << "][" << r << "]=" << DualValueCon14_ZZY_kr[k][r] << endl;
		l++;
	}


	return 0;
}
int GetExtremePointOfDSP(IloCplex cplexSlave_ptr, IloNum OptDualValues, IloRangeMatrix4x4 Con9_ZZZX_ijrm, IloRangeMatrix2x2 Con10a_ZZY_ir, IloRangeMatrix2x2 Con10b_ZZY_ir, IloRangeMatrix4x4 Con11a_ZX_ijrm, IloRangeMatrix4x4 Con11b_ZX_ijrm, IloRangeArray Con12_ZZY_n, IloRangeArray Con13_ZZY_r, IloRangeArray Con14_ZZY_r, int k, bool AllAreZero) {
	//---------------------Get an extreme point of DUAL SLAVE problem--------------------
	//cout << "ETREME POINT:" << endl;
	for (r = 0; r < rmax; r++) {
		for (i = 0; i < imax; i++) {
			for (j = 1; j < jmax + 1; j++) {
				for (m = 0; m < mmax; m++) {
					OptDualValues = cplexSlave_ptr.getDual(Con9_ZZZX_ijrm[i][j - 1][r][m]);
					DualValueCon9_ZZZX_ijkrm[i][j][k][r][m] = OptDualValues;
					if (DualValueCon9_ZZZX_ijkrm[i][j][k][r][m] != 0) AllAreZero = false;
					//if (DualValueCon9_ZZZX_ijkrm[i][j][k][r][m] != 0)cout << "DualValueCon9_ZZZX_ijkrm[" << i << "][" << j << "][" << k << "][" << r << "][" << m << "]=" << DualValueCon9_ZZZX_ijkrm[i][j][k][r][m] << endl;
				}
			}
		}
		for (i = 0; i < imax + 1; i++) {
			OptDualValues = cplexSlave_ptr.getDual(Con10a_ZZY_ir[i][r]);
			DualValueCon10a_ZZY_ikr[i][k][r] = OptDualValues;
			if (DualValueCon10a_ZZY_ikr[i][k][r] != 0) AllAreZero = false;
			//if (DualValueCon10a_ZZY_ikr[i][k][r] != 0)cout << "DualValueCon10a_ZZY_ikr[" << i << "][" << k << "][" << r << "]=" << DualValueCon10a_ZZY_ikr[i][k][r] << endl;
			OptDualValues = cplexSlave_ptr.getDual(Con10b_ZZY_ir[i][r]);
			DualValueCon10b_ZZY_ikr[i][k][r] = OptDualValues;
			if (DualValueCon10b_ZZY_ikr[i][k][r] != 0) AllAreZero = false;
			//if (DualValueCon10b_ZZY_ikr[i][k][r] != 0)cout << "DualValueCon10b_ZZY_ikr[" << i << "][" << k << "][" << r << "]=" << DualValueCon10b_ZZY_ikr[i][k][r] << endl;
			for (j = 0; j < jmax + 1; j++) {
				for (m = 0; m < mmax; m++) {
					OptDualValues = cplexSlave_ptr.getDual(Con11b_ZX_ijrm[i][j][r][m]);
					DualValueCon11b_ZX_ijkrm[i][j][k][r][m] = OptDualValues;
					if (DualValueCon11b_ZX_ijkrm[i][j][k][r][m] != 0) AllAreZero = false;
					//if (DualValueCon11b_ZX_ijkrm[i][j][k][r][m] != 0)cout << "DualValueCon11b_ZX_ijkrm[" << i << "][" << j << "][" << k << "][" << r << "][" << m << "]=" << DualValueCon11b_ZX_ijkrm[i][j][k][r][m] << endl;
					if (m > 0) {
						OptDualValues = cplexSlave_ptr.getDual(Con11a_ZX_ijrm[i][j][r][m - 1]);
						DualValueCon11a_ZX_ijkrm[i][j][k][r][m] = OptDualValues;
						if (DualValueCon11a_ZX_ijkrm[i][j][k][r][m] != 0) AllAreZero = false;
						//if (DualValueCon11a_ZX_ijkrm[i][j][k][r][m] != 0)cout << "DualValueCon11a_ZX_ijkrm[" << i << "][" << j << "][" << k << "][" << r << "][" << m << "]=" << DualValueCon11a_ZX_ijkrm[i][j][k][r][m] << endl;
					}
				}
			}
		}
		if (r > 0) {
			OptDualValues = cplexSlave_ptr.getDual(Con13_ZZY_r[r - 1]);
			DualValueCon13_ZZY_kr[k][r] = OptDualValues;
			if (DualValueCon13_ZZY_kr[k][r] != 0) AllAreZero = false;
			//if (DualValueCon13_ZZY_kr[k][r] != 0)cout << "DualValueCon13_ZZY_kr[" << k << "][" << r << "]=" << DualValueCon13_ZZY_kr[k][r] << endl;
		}
		OptDualValues = cplexSlave_ptr.getDual(Con14_ZZY_r[r]);
		DualValueCon14_ZZY_kr[k][r] = OptDualValues;
		if (DualValueCon14_ZZY_kr[k][r] != 0) AllAreZero = false;
		//if (DualValueCon14_ZZY_kr[k][r] != 0)cout << "DualValueCon14_ZZY_kr[" << k << "][" << r << "]=" << DualValueCon14_ZZY_kr[k][r] << endl;
	}
	OptDualValues = cplexSlave_ptr.getDual(Con12_ZZY_n[0]);
	DualValueCon12_ZZY_k[k] = OptDualValues;
	if (DualValueCon12_ZZY_k[k] != 0) AllAreZero = false;
	//if (DualValueCon12_ZZY_k[k] != 0)cout << "DualValueCon12_ZZY_k[" << k << "]=" << DualValueCon12_ZZY_k[k] << endl;




	//for (i = 0; i < imax; i++) {
	//	for (j = 1; j < jmax + 1; j++) {
	//		for (r = 0; r < rmax; r++) {
	//			for (m = 0; m < mmax; m++) {
	//				//OptDualValues = cplexSlave_ptr.getDual(Con9_ZZZX_ijrm[i][j - 1][r][m]);
	//				//DualValueCon9_ZZZX_ijkrm[i][j][k][r][m] = OptDualValues;
	//				if (DualValueCon9_ZZZX_ijkrm[i][j][k][r][m] != 0)cout << "DualValueCon9_ZZZX_ijkrm[" << i << "][" << j << "][" << k << "][" << r << "][" << m << "]=" << DualValueCon9_ZZZX_ijkrm[i][j][k][r][m] << endl;

	//			}
	//		}
	//	}
	//}
	//for (i = 0; i < imax + 1; i++) {
	//	for (r = 0; r < rmax; r++) {
	//		//OptDualValues = cplexSlave_ptr.getDual(Con10a_ZZY_ir[i][r]);
	//		//DualValueCon10a_ZZY_ikr[i][k][r] = OptDualValues;
	//		if (DualValueCon10a_ZZY_ikr[i][k][r] != 0)cout << "DualValueCon10a_ZZY_ikr[" << i << "][" << k << "][" << r << "]=" << DualValueCon10a_ZZY_ikr[i][k][r] << endl;
	//		//OptDualValues = cplexSlave_ptr.getDual(Con10b_ZZY_ir[i][r]);
	//		//DualValueCon10b_ZZY_ikr[i][k][r] = OptDualValues;
	//		if (DualValueCon10b_ZZY_ikr[i][k][r] != 0)cout << "DualValueCon10b_ZZY_ikr[" << i << "][" << k << "][" << r << "]=" << DualValueCon10b_ZZY_ikr[i][k][r] << endl;
	//	}
	//}

	//for (i = 0; i < imax + 1; i++) {
	//	for (j = 0; j < jmax + 1; j++) {
	//		for (r = 0; r < rmax; r++) {
	//			for (m = 0; m < mmax; m++) {
	//				//OptDualValues = cplexSlave_ptr.getDual(Con11b_ZX_ijrm[i][j][r][m]);
	//				//DualValueCon11b_ZX_ijkrm[i][j][k][r][m] = OptDualValues;
	//				if (DualValueCon11b_ZX_ijkrm[i][j][k][r][m] != 0)cout << "DualValueCon11b_ZX_ijkrm[" << i << "][" << j << "][" << k << "][" << r << "][" << m << "]=" << DualValueCon11b_ZX_ijkrm[i][j][k][r][m] << endl;
	//				if (m > 0) {
	//					//OptDualValues = cplexSlave_ptr.getDual(Con11a_ZX_ijrm[i][j][r][m - 1]);
	//					//DualValueCon11a_ZX_ijkrm[i][j][k][r][m] = OptDualValues;
	//					if (DualValueCon11a_ZX_ijkrm[i][j][k][r][m] != 0)cout << "DualValueCon11a_ZX_ijkrm[" << i << "][" << j << "][" << k << "][" << r << "][" << m << "]=" << DualValueCon11a_ZX_ijkrm[i][j][k][r][m] << endl;
	//				}
	//			}
	//		}
	//	}
	//}

	////OptDualValues = cplexSlave_ptr.getDual(Con12_ZZY_n[0]);
	////DualValueCon12_ZZY_k[k] = OptDualValues;
	//if (DualValueCon12_ZZY_k[k] != 0)cout << "DualValueCon12_ZZY_k[" << k << "]=" << DualValueCon12_ZZY_k[k] << endl;
	//for (r = 0; r < rmax; r++) {
	//	if (r > 0) {
	//		//OptDualValues = cplexSlave_ptr.getDual(Con13_ZZY_r[r - 1]);
	//		//DualValueCon13_ZZY_kr[k][r] = OptDualValues;
	//		if (DualValueCon13_ZZY_kr[k][r] != 0)cout << "DualValueCon13_ZZY_kr[" << k << "][" << r << "]=" << DualValueCon13_ZZY_kr[k][r] << endl;
	//	}
	//	//OptDualValues = cplexSlave_ptr.getDual(Con14_ZZY_r[r]);
	//	//DualValueCon14_ZZY_kr[k][r] = OptDualValues;
	//	if (DualValueCon14_ZZY_kr[k][r] != 0)cout << "DualValueCon14_ZZY_kr[" << k << "][" << r << "]=" << DualValueCon14_ZZY_kr[k][r] << endl;
	//}


	return 0;
}
int CreateBendersFeasCut(int FeasOrOpt, IloExpr expr101, IloNumVarMatrix5x5 X_ijkrm, IloNumVarMatrix3x3 Y_ikr, IloNumVarArray Heta_k, int k, int k_prime) {
	//---------CREATION OF BENDERS CUT--------------- 
	//If FeasOrOpt=0, then a FEASIBILITY CUT is created
	//If FeasOrOpt=1, then a OPTIMALITY CUT is created

	for (r = 0; r < rmax; r++) {
		for (i = 0; i < imax; i++) {
			for (j = 1; j < jmax + 1; j++) {
				for (m = 0; m < mmax; m++) {
					expr101 += DualValueCon9_ZZZX_ijkrm[i][j][k][r][m] * (-((1 - X_ijkrm[i][j][k_prime][r][m]) * Big_M - zeta_ijm[i][j][m] - s_i[j]));
				}
			}
		}
		for (i = 0; i < imax + 1; i++) {
			expr101 += DualValueCon10a_ZZY_ikr[i][k][r] * ((e_i[i] + s_i[i]) * Y_ikr[i][k_prime][r]);
			expr101 += DualValueCon10b_ZZY_ikr[i][k][r] * (-(l_i[i] + s_i[i]) * Y_ikr[i][k_prime][r]);
			for (j = 0; j < jmax + 1; j++) {
				for (m = 0; m < mmax; m++) {
					expr101 += DualValueCon11b_ZX_ijkrm[i][j][k][r][m] * (-(w_ijm[i][j][m] * X_ijkrm[i][j][k_prime][r][m] + (1 - X_ijkrm[i][j][k_prime][r][m]) * Big_M));
					if (m > 0) {
						expr101 += DualValueCon11a_ZX_ijkrm[i][j][k][r][m] * (w_ijm[i][j][m - 1] * X_ijkrm[i][j][k_prime][r][m] - (1 - X_ijkrm[i][j][k_prime][r][m]) * Big_M);
					}
				}
			}
		}
		if (r > 0) {
			for (i = 1; i < imax; i++) {
				expr101 += DualValueCon13_ZZY_kr[k][r] * (lamda * s_i[i] * Y_ikr[i][k_prime][r]);
			}
		}
		for (i = 1; i < imax; i++) {
			expr101 += DualValueCon14_ZZY_kr[k][r] * (lamda * s_i[i] * Y_ikr[i][k_prime][r]);
		}
		expr101 += DualValueCon14_ZZY_kr[k][r] * (-MaxTripDuration);

	}

	for (i = 1; i < imax; i++) {
		expr101 += DualValueCon12_ZZY_k[k] * (lamda * s_i[i] * Y_ikr[i][k_prime][0]);
	}

	if (FeasOrOpt == 1) {//then create an Optimality cut
		//for (n = 0; n < 1; n++) {
		expr101 -= Heta_k[k_prime];
		//}
		//for (k = 0; k < kmax; k++) {
		//	for (r = 0; r < rmax; r++) {
		//		for (j = 0; j < jmax + 1; j++) {
		//			for (m = 0; m < mmax; m++) {
		//				for (i = 0; i < imax + 1; i++) {
		//					expr101 -= g * TravelTimeMinimum_ijm[i][j][m] * X_ijkrmValue[i][j][k][r][m];
		//				}
		//			}
		//		}
		//		//expr1 += g * ZZ_ikr[imax][k][r];
		//	}
		//}
	}

	return 0;
}
int CreateBendersOptCut(int FeasOrOpt, IloExpr expr101, IloNumVarMatrix5x5 X_ijkrm, IloNumVarMatrix3x3 Y_ikr, IloNumVarArray Heta_k, int k, int k_prime) {
	//---------CREATION OF BENDERS CUT--------------- 
	//If FeasOrOpt=0, then a FEASIBILITY CUT is created
	//If FeasOrOpt=1, then a OPTIMALITY CUT is created
	//for (k = 0; k < kmax; k++) {
	for (r = 0; r < rmax; r++) {
		for (i = 0; i < imax; i++) {
			for (j = 1; j < jmax + 1; j++) {
				for (m = 0; m < mmax; m++) {
					expr101 += DualValueCon9_ZZZX_ijkrm[i][j][k][r][m] * (-((1 - X_ijkrm[i][j][k_prime][r][m]) * Big_M - zeta_ijm[i][j][m] - s_i[j]));
					//if (DualValueCon9_ZZZX_ijkrm[i][j][k][r][m] != 0)cout << "DualValueCon9_ZZZX_ijkrm[" << i << "][" << j << "][" << k << "][" << r << "][" << m << "]=" << DualValueCon9_ZZZX_ijkrm[i][j][k][r][m] << endl;
				}
			}
		}
		for (i = 0; i < imax + 1; i++) {
			expr101 += DualValueCon10a_ZZY_ikr[i][k][r] * ((e_i[i] + s_i[i]) * Y_ikr[i][k_prime][r]);
			expr101 += DualValueCon10b_ZZY_ikr[i][k][r] * (-(l_i[i] + s_i[i]) * Y_ikr[i][k_prime][r]);
			//if (DualValueCon10a_ZZY_ikr[i][k][r] != 0)cout << "DualValueCon10a_ZZY_ikr[" << i << "][" << k << "][" << r << "]=" << DualValueCon10a_ZZY_ikr[i][k][r] << endl;
			//if (DualValueCon10b_ZZY_ikr[i][k][r] != 0)cout << "DualValueCon10b_ZZY_ikr[" << i << "][" << k << "][" << r << "]=" << DualValueCon10b_ZZY_ikr[i][k][r] << endl;
			for (j = 0; j < jmax + 1; j++) {
				for (m = 0; m < mmax; m++) {
					expr101 += DualValueCon11b_ZX_ijkrm[i][j][k][r][m] * (-(w_ijm[i][j][m] * X_ijkrm[i][j][k_prime][r][m] + (1 - X_ijkrm[i][j][k_prime][r][m]) * Big_M));
					//if (DualValueCon11b_ZX_ijkrm[i][j][k][r][m] != 0)cout << "DualValueCon11b_ZX_ijkrm[" << i << "][" << j << "][" << k << "][" << r << "][" << m << "]=" << DualValueCon11b_ZX_ijkrm[i][j][k][r][m] << endl;
					if (m > 0) {
						expr101 += DualValueCon11a_ZX_ijkrm[i][j][k][r][m] * (w_ijm[i][j][m - 1] * X_ijkrm[i][j][k_prime][r][m] - (1 - X_ijkrm[i][j][k_prime][r][m]) * Big_M);
						//if (DualValueCon11a_ZX_ijkrm[i][j][k][r][m] != 0)cout << "DualValueCon11a_ZX_ijkrm[" << i << "][" << j << "][" << k << "][" << r << "][" << m << "]=" << DualValueCon11a_ZX_ijkrm[i][j][k][r][m] << endl;
					}

				}
			}
		}
		if (r > 0) {
			for (i = 1; i < imax; i++) {
				expr101 += DualValueCon13_ZZY_kr[k][r] * (lamda * s_i[i] * Y_ikr[i][k_prime][r]);
			}
			//if (DualValueCon13_ZZY_kr[k][r] != 0)cout << "DualValueCon13_ZZY_kr[" << k << "][" << r << "]=" << DualValueCon13_ZZY_kr[k][r] << endl;
		}
		for (i = 1; i < imax; i++) {
			expr101 += DualValueCon14_ZZY_kr[k][r] * (lamda * s_i[i] * Y_ikr[i][k_prime][r]);
		}
		expr101 += DualValueCon14_ZZY_kr[k][r] * (-MaxTripDuration);
		//if (DualValueCon14_ZZY_kr[k][r] != 0)cout << "DualValueCon14_ZZY_kr[" << k << "][" << r << "]=" << DualValueCon14_ZZY_kr[k][r] << endl;
	}
	for (i = 1; i < imax; i++) {
		expr101 += DualValueCon12_ZZY_k[k] * (lamda * s_i[i] * Y_ikr[i][k_prime][0]);
		//if (DualValueCon12_ZZY_k[k] != 0)cout << "DualValueCon12_ZZY_k[" << k << "]=" << DualValueCon12_ZZY_k[k] << endl;
	}
	//}
	if (FeasOrOpt == 1) {//then create an Optimality cut
		//for (n = 0; n < 1; n++) {
		expr101 -= Heta_k[k_prime];
		//}
		//for (k = 0; k < kmax; k++) {
		//	for (r = 0; r < rmax; r++) {
		//		for (j = 0; j < jmax + 1; j++) {
		//			for (m = 0; m < mmax; m++) {
		//				for (i = 0; i < imax + 1; i++) {
		//					if (X_ijkrmValue[i][j][k][r][m] == 1) {
		//						expr101 -= g * TravelTimeMinimum_ijm[i][j][m] * X_ijkrm[i][j][k][r][m];
		//					}
		//				}
		//			}
		//		}
		//		//expr1 += g * ZZ_ikr[imax][k][r];
		//	}
		//}
	}


	return 0;
}
int AddBendersCutToMaster(IloEnv env, int FeasOrOpt, IloExpr expr101, int loop, IloModel modelMaster_ptr, IloRangeArray BendersCuts) {
	//--------------ADD BENDERS  CUT TO MASTER----------------
	//If FeasOrOpt=0, then a FEASIBILITY CUT is added
	//If FeasOrOpt=1, then a OPTIMALITY CUT is added
	char MasterCut[90];

	if (FeasOrOpt == 0) {
		sprintf(MasterCut, "FeasibilityCut(iter%d)", loop);
		BDFeasCuts++;
	}
	else if (FeasOrOpt == 1) {
		sprintf(MasterCut, "OptimalityCut(iter%d)", loop);
		BDOptCuts++;
	}

	double LB101 = -IloInfinity, UB101 = 0;
	IloRange CTMaster(env, LB101, expr101, UB101, MasterCut);
	BendersCuts.add(CTMaster);
	modelMaster_ptr.add(CTMaster);
	CutsPerIteration++;

	return 0;
}
int CreateAddAuxFeasibilityCutToMaster(IloEnv env, int loop, IloModel modelMaster_ptr, IloNumVarMatrix3x3 Y_ikr, IloRangeMatrix2x2 AuxFeasCut_kr) {
	//--------------ADD AUXILIARY FEASIBILITY CUT TO MASTER---------------
	double LBAuxSlaveCon = 0;
	double UBAuxSlaveCon = 0;
	char CharAuxSlaveCon[90];
	//-------------------------- Constraint AuxFeasCut_kr -------------------------
	for (k = 0; k < kmax; k++) {
		IloRangeArray AuxFeasCut_r(env, 0);
		for (r = 0; r < rmax; r++) {
			IloExpr expr(env, 0);
			int NoOfNodesInTour = 0;
			for (i = 1; i < imax; i++) {
				expr += Y_ikr[i][k][r] * Y_iValue[i];
				if (Y_iValue[i] != 0) NoOfNodesInTour++;
			}
			sprintf(CharAuxSlaveCon, "AuxFeasCut_kr(iter%d)(k%d,r%d)", loop, k, r);
			LBAuxSlaveCon = -IloInfinity, UBAuxSlaveCon = NoOfNodesInTour - 1;
			IloRange AuxFeasCut(env, LBAuxSlaveCon, expr, UBAuxSlaveCon, CharAuxSlaveCon);
			AuxFeasCuts++;
			modelMaster_ptr.add(AuxFeasCut);
			AuxFeasCut_r.add(AuxFeasCut);
			expr.end();
		}
		AuxFeasCut_kr.add(AuxFeasCut_r);
	}


	return 0;
}
int CreateAlternativeDualSolution(int NoOfOptCut, int NoOfAlternativeSolutions) {
	int imax_plus = imax + 1;
	int jmax_plus = jmax + 1;
	bool***** ChangedDualValueCon9_ZZZX_ijkrm;
	bool*** ChangedDualValueCon10a_ZZY_ikr;
	bool*** ChangedDualValueCon10b_ZZY_ikr;
	bool***** ChangedDualValueCon11a_ZX_ijkrm;
	bool***** ChangedDualValueCon11b_ZX_ijkrm;
	bool* ChangedDualValueCon12_ZZY_k;
	bool** ChangedDualValueCon13_ZZY_kr;
	bool** ChangedDualValueCon14_ZZY_kr;
	ChangedDualValueCon12_ZZY_k = new bool[kmax];
	ChangedDualValueCon13_ZZY_kr = new bool* [kmax];
	ChangedDualValueCon14_ZZY_kr = new bool* [kmax];
	for (k = 0; k < kmax; k++) {
		ChangedDualValueCon13_ZZY_kr[k] = new bool[rmax];
		ChangedDualValueCon14_ZZY_kr[k] = new bool[rmax];
		ChangedDualValueCon12_ZZY_k[k] = false;
		for (r = 0; r < rmax; r++) {
			ChangedDualValueCon13_ZZY_kr[k][r] = false;
			ChangedDualValueCon14_ZZY_kr[k][r] = false;
		}

	}
	ChangedDualValueCon9_ZZZX_ijkrm = new bool**** [imax_plus];
	ChangedDualValueCon11a_ZX_ijkrm = new bool**** [imax_plus];
	ChangedDualValueCon11b_ZX_ijkrm = new bool**** [imax_plus];
	ChangedDualValueCon10a_ZZY_ikr = new bool** [imax_plus];
	ChangedDualValueCon10b_ZZY_ikr = new bool** [imax_plus];
	for (i = 0; i < imax_plus; i++) {
		ChangedDualValueCon9_ZZZX_ijkrm[i] = new bool*** [jmax_plus];
		ChangedDualValueCon11a_ZX_ijkrm[i] = new bool*** [jmax_plus];
		ChangedDualValueCon11b_ZX_ijkrm[i] = new bool*** [jmax_plus];
		ChangedDualValueCon10a_ZZY_ikr[i] = new bool* [kmax];
		ChangedDualValueCon10b_ZZY_ikr[i] = new bool* [kmax];
	}
	for (i = 0; i < imax_plus; i++) {
		for (j = 0; j < jmax_plus; j++) {
			ChangedDualValueCon9_ZZZX_ijkrm[i][j] = new bool** [kmax];
			ChangedDualValueCon11a_ZX_ijkrm[i][j] = new bool** [kmax];
			ChangedDualValueCon11b_ZX_ijkrm[i][j] = new bool** [kmax];
		}
		for (k = 0; k < kmax; k++) {
			ChangedDualValueCon10a_ZZY_ikr[i][k] = new bool[rmax];
			ChangedDualValueCon10b_ZZY_ikr[i][k] = new bool[rmax];
			for (r = 0; r < rmax; r++) {
				ChangedDualValueCon10a_ZZY_ikr[i][k][r] = false;
				ChangedDualValueCon10b_ZZY_ikr[i][k][r] = false;
			}
		}
	}

	for (i = 0; i < imax_plus; i++) {
		for (j = 0; j < jmax_plus; j++) {
			for (k = 0; k < kmax; k++) {
				ChangedDualValueCon9_ZZZX_ijkrm[i][j][k] = new bool* [rmax];
				ChangedDualValueCon11a_ZX_ijkrm[i][j][k] = new bool* [rmax];
				ChangedDualValueCon11b_ZX_ijkrm[i][j][k] = new bool* [rmax];
			}
		}
	}
	for (i = 0; i < imax_plus; i++) {
		for (j = 0; j < jmax_plus; j++) {
			for (k = 0; k < kmax; k++) {
				for (r = 0; r < rmax; r++) {
					ChangedDualValueCon9_ZZZX_ijkrm[i][j][k][r] = new bool[mmax];
					ChangedDualValueCon11a_ZX_ijkrm[i][j][k][r] = new bool[mmax];
					ChangedDualValueCon11b_ZX_ijkrm[i][j][k][r] = new bool[mmax];
					for (m = 0; m < mmax; m++) {
						ChangedDualValueCon9_ZZZX_ijkrm[i][j][k][r][m] = false;
						ChangedDualValueCon11a_ZX_ijkrm[i][j][k][r][m] = false;
						ChangedDualValueCon11b_ZX_ijkrm[i][j][k][r][m] = false;
					}
				}
			}
		}
	}





	for (k = 0; k < kmax; k++) {
		for (r = 0; r < rmax; r++) {
			for (i = 0; i < imax; i++) {
				for (j = 1; j < jmax + 1; j++) {
					for (m = 0; m < mmax; m++) {
						if (NoOfOptCut < NoOfAlternativeSolutions && DualValueCon9_ZZZX_ijkrm[i][j][k][r][m] != 0 && ChangedDualValueCon9_ZZZX_ijkrm[i][j][k][r][m] == false) {
							for (int l = 0; l < kmax; l++) {
								if (l != k) {
									DualValueCon9_ZZZX_ijkrm[i][j][l][r][m] = DualValueCon9_ZZZX_ijkrm[i][j][k][r][m];
									DualValueCon9_ZZZX_ijkrm[i][j][k][r][m] = 0;
									ChangedDualValueCon9_ZZZX_ijkrm[i][j][l][r][m] = true;
								}
							}
						}
					}
				}
			}
			for (i = 0; i < imax + 1; i++) {
				if (NoOfOptCut < NoOfAlternativeSolutions && DualValueCon10a_ZZY_ikr[i][k][r] != 0 && ChangedDualValueCon10a_ZZY_ikr[i][k][r] == false) {
					for (int l = 0; l < kmax; l++) {
						if (l != k) {
							DualValueCon10a_ZZY_ikr[i][l][r] = DualValueCon10a_ZZY_ikr[i][k][r];
							DualValueCon10a_ZZY_ikr[i][k][r] = 0;
							ChangedDualValueCon10a_ZZY_ikr[i][l][r] = true;
						}
					}
				}
				if (NoOfOptCut < NoOfAlternativeSolutions && DualValueCon10b_ZZY_ikr[i][k][r] != 0 && ChangedDualValueCon10b_ZZY_ikr[i][k][r] == false) {
					for (int l = 0; l < kmax; l++) {
						if (l != k) {
							DualValueCon10b_ZZY_ikr[i][l][r] = DualValueCon10b_ZZY_ikr[i][k][r];
							DualValueCon10b_ZZY_ikr[i][k][r] = 0;
							ChangedDualValueCon10b_ZZY_ikr[i][l][r] = true;
						}

					}
				}
				for (j = 0; j < jmax + 1; j++) {
					for (m = 0; m < mmax; m++) {
						if (NoOfOptCut < NoOfAlternativeSolutions && DualValueCon11b_ZX_ijkrm[i][j][k][r][m] != 0 && ChangedDualValueCon11b_ZX_ijkrm[i][j][k][r][m] == false) {
							for (int l = 0; l < kmax; l++) {
								if (l != k) {
									DualValueCon11b_ZX_ijkrm[i][j][l][r][m] = DualValueCon11b_ZX_ijkrm[i][j][k][r][m];
									DualValueCon11b_ZX_ijkrm[i][j][k][r][m] = 0;
									ChangedDualValueCon11b_ZX_ijkrm[i][j][l][r][m] = true;
								}

							}
						}
						if (m > 0) {
							if (NoOfOptCut < NoOfAlternativeSolutions && DualValueCon11a_ZX_ijkrm[i][j][k][r][m] != 0 && ChangedDualValueCon11a_ZX_ijkrm[i][j][k][r][m] == false) {
								for (int l = 0; l < kmax; l++) {
									if (l != k) {
										DualValueCon11a_ZX_ijkrm[i][j][l][r][m] = DualValueCon11a_ZX_ijkrm[i][j][k][r][m];
										DualValueCon11a_ZX_ijkrm[i][j][k][r][m] = 0;
										ChangedDualValueCon11a_ZX_ijkrm[i][j][l][r][m] = true;
									}

								}
							}
						}

					}
				}
			}
			if (r > 0) {
				for (i = 1; i < imax; i++) {
					if (NoOfOptCut < NoOfAlternativeSolutions && DualValueCon13_ZZY_kr[k][r] != 0 && ChangedDualValueCon13_ZZY_kr[k][r] == false) {
						for (int l = 0; l < kmax; l++) {
							if (l != k) {
								DualValueCon13_ZZY_kr[l][r] = DualValueCon13_ZZY_kr[k][r];
								DualValueCon13_ZZY_kr[k][r] = 0;
								ChangedDualValueCon13_ZZY_kr[l][r] = true;
							}

						}
					}
				}
			}
			if (NoOfOptCut < NoOfAlternativeSolutions && DualValueCon14_ZZY_kr[k][r] != 0 && ChangedDualValueCon14_ZZY_kr[k][r] == false) {
				for (int l = 0; l < kmax; l++) {
					if (l != k) {
						DualValueCon14_ZZY_kr[l][r] = DualValueCon14_ZZY_kr[k][r];
						DualValueCon14_ZZY_kr[k][r] = 0;
						ChangedDualValueCon14_ZZY_kr[l][r] = true;
					}

				}
			}
		}
		for (i = 1; i < imax; i++) {
			if (NoOfOptCut < NoOfAlternativeSolutions && DualValueCon12_ZZY_k[k] != 0 && ChangedDualValueCon12_ZZY_k[k] == false) {
				for (int l = 0; l < kmax; l++) {
					if (l != k) {
						DualValueCon12_ZZY_k[l] = DualValueCon12_ZZY_k[k];
						DualValueCon12_ZZY_k[k] = 0;
						ChangedDualValueCon12_ZZY_k[l] = true;
					}

				}
			}
		}
	}

	return 0;
}
int PrintCurrentMasterSolution(int loop_ptr, char* FilePath_Results_ptr, int** RouteIsUsed_ptr) {
	int status, test = 0;
	char* FileName_ptr;
	char filepath[1024];
	char FileName_Problem_ptr[6];
	if (FileName_Problem[1] == 'c') {
		memcpy(FileName_Problem_ptr, &FileName_Problem[0], 5);
		FileName_Problem_ptr[5] = '\0';
	}
	else {
		memcpy(FileName_Problem_ptr, &FileName_Problem[0], 4);
		FileName_Problem_ptr[4] = '\0';
	}
	//cout << FileName_Problem_ptr << endl;
	sprintf(filepath, "%s/%s", FilePath_Results_ptr, FileName_Problem_ptr);
	//string stringpath = filepath;
	status = mkdir(filepath);
	sprintf(filepath, "%s/%s/CurrentMasterSolution", FilePath_Results_ptr, FileName_Problem_ptr);
	status = mkdir(filepath);
	sprintf(filepath, "%s/%s/CurrentMasterSolution/%s_CurrentMasterSolution%d.txt", FilePath_Results_ptr, FileName_Problem_ptr, FileName_Problem_ptr, loop_ptr);
	outfile.open(filepath);
	for (i = 0; i < imax + 1; i++) {
		for (j = 0; j < jmax + 1; j++) {
			X_ijValue[i][j] = 0;
			for (k = 0; k < kmax; k++) {
				for (r = 0; r < rmax; r++) {
					for (m = 0; m < mmax; m++) {
						if (X_ijkrmValue[i][j][k][r][m] >= 0.01) {
							outfile << "X_ijkrm[" << i << "][" << j << "][" << k << "][" << r << "][" << m << "]=" << X_ijkrmValue[i][j][k][r][m] << endl;
							RouteIsUsed_ptr[k][r] = 1;
							X_ijValue[i][j] = X_ijValue[i][j] + X_ijkrmValue[i][j][k][r][m];
						}
					}
				}
			}
			//if (X_ijValue[i][j] >= 0.01) cout << "X_ij[" << i << "][" << j << "]=" << X_ijValue[i][j] << endl;
		}
	}
	outfile.close();

	return 0;
}
int BendersIteration(IloEnv env, IloModel modelMaster_ptr, IloModel modelSlave_ptr, IloNumVarMatrix5x5 X_ijkrm, IloNumVarMatrix3x3 Y_ikr, IloNumVarArray Heta_k, IloRangeMatrix2x2 Con2_YX_kr, IloRangeMatrix2x2 Con3_YX_kr, IloRangeMatrix3x3 Con4a_YX_ikr, IloRangeMatrix3x3 Con4b_YX_ikr, IloRangeArray Con5_Y_i, IloRangeMatrix2x2 Con6_Y_kr, IloRangeMatrix4x4 Con15_XX_ikrm, IloRangeMatrix5x5 Con16_X_ijkrm, IloRangeArray ConAuxiliary_i, IloNumVarMatrix2x2 ZZ_ir, IloRangeMatrix4x4 Con9_ZZZX_ijrm, IloRangeMatrix2x2 Con10a_ZZY_ir, IloRangeMatrix2x2 Con10b_ZZY_ir, IloRangeMatrix4x4 Con11a_ZX_ijrm, IloRangeMatrix4x4 Con11b_ZX_ijrm, IloRangeArray Con12_ZZY_n, IloRangeArray Con13_ZZY_r, IloRangeArray Con14_ZZY_r, IloRangeArray BendersCuts, IloNum OptDualValues, IloNumArray FeasDualValues, char* FilePath_Results_ptr, int* loop_iter, IloModel modelAuxSlave, IloNumVarMatrix3x3 X_aux_ijm, IloNumVarArray ZZ_aux_i, IloRangeArray Con2_aux_YX_n, IloRangeArray Con3_aux_YX_n, IloRangeArray Con4a_aux_YX_i, IloRangeArray Con4b_aux_YX_i, IloRangeMatrix3x3 Con9_aux_ZZZX_ijm, IloRangeArray Con10a_aux_ZZY_i, IloRangeArray Con10b_aux_ZZY_i, IloRangeMatrix3x3 Con11a_aux_ZX_ijm, IloRangeMatrix3x3 Con11b_aux_ZX_ijm, IloRangeArray Con14_aux_ZZY_n, IloRangeMatrix2x2 AuxFeasCut_kr) {

	bool InfeasibleMaster = false;
	bool AllSlavesFeasible = true;
	int* SlaveIsFeasible;
	SlaveIsFeasible = new int[kmax];
	int loop = 0, status;
	int  startPrint = 0, stopPrint = 0;
	int CoveredVariables;
	IloCplex cplexSlave_ptr(env);
	IloCplex cplexMaster_ptr(env);
	IloCplex cplexAuxSlave_ptr(env);

	cplexSlave_ptr.extract(modelSlave_ptr);
	cplexSlave_ptr.exportModel("modelSlave1.lp");

	cplexMaster_ptr.extract(modelMaster_ptr);
	if (imax < 20) cplexMaster_ptr.exportModel("modelMaster1.lp");//

	double DTransposeY = 0, TotalSlaveObjFunction = 0;
	double* SlaveObjFunction;
	SlaveObjFunction = new double[kmax];
	double BestSlaveObj = 100;

	int MinNodesInSubtour = imax + 1;
	int MaxNodesInSubtour = 0;
	int Sub = -1;
	int NonSub = -1;
	SECIterations = 0;//Number of iterations for generating SECs
	SECNumber = 0;//Total number of SEC generated

	LowerBoundArray.clear();
	UpperBoundArray.clear();
	UpperBoundGlobalArray.clear();
	LowerBoundGlobalArray.clear();
	dTy.clear();
	zCurrent.clear();
	cTx.clear();
	BestSlaveObjSoFar.clear();
	Time.clear();
	SlackValuesOfBendersCuts.clear();
	SlackValuesOfMainMasterCons.clear();
	NoOfCutsInEachIteration.clear();

	epsilon = 0.01;
	MaxNoOfMultiSol = 5;
	MultiInfeasSolutions = 0;
	MultiFeasSolutions = 0;
	UpperBound = Big_M;
	LowerBound = -Big_M;
	UpperBoundGlobal = Big_M;
	LowerBoundGlobal = -Big_M;
	Gap = 1;
	SolutionStatus;
	MinStopTime = imax;
	StopGapMaster = 0;//Optimality Gap to stop the code
	StopTime = MinStopTime;//Seconds to stop the code
	fraction = 0.90;
	BDFeasCuts = 0;
	BDOptCuts = 0;
	AuxFeasCuts = 0;
	StopTimeAuxSlave = 2 * imax;//Seconds to stop solving the auxiliary slave problem
	GapAuxSlave = 0;;//Optimality gap at the solution of auxiliary slave problem


	OptimalOriginalObjFunction = 0;
	OptimalMasterObjFunction = 0;
	OptimalSlaveObjFunction = 0;
	SolutionStatus = 0;//Infeasible
	MaxMaxNoOfMultiSol = imax * 2;

	while (Gap > epsilon && loop < 10000 && ((clock() - start) / CLOCKS_PER_SEC) < MaxBendersDuration) {
		if (((clock() - start) / CLOCKS_PER_SEC) + 2 * StopTime > MaxBendersDuration) StopTime = (MaxBendersDuration - (clock() - start) / CLOCKS_PER_SEC) / 2.0;
		loop++;
		cout << "-----------------" << endl;
		cout << "Iteration =" << loop << endl;
		cout << "-----------------" << endl;
		CutsPerIteration = 0;
		CoveredVariables = 0;
		DTransposeY = 0;
		bool SubtoursExist = true;
		int** SubtoursNodes;
		int** NonSubtoursNodes;
		SubtoursNodes = new int* [imax + 1];
		NonSubtoursNodes = new int* [imax + 1];
		for (i = 0; i < imax + 1; i++) {
			SubtoursNodes[i] = new int[jmax + 1];
			NonSubtoursNodes[i] = new int[jmax + 1];
		}
		int* NodesInSubtour;
		NodesInSubtour = new int[imax + 1];
		int* NodesInNonSubtour;
		NodesInNonSubtour = new int[imax + 1];
		//shortest subtour distance
		double ShortestSubtourDistance = Big_M * Big_M;
		double* SubtourDistance;
		SubtourDistance = new double[imax + 1];
		while (SubtoursExist == true) {
			//cout << "SECIterations =" << SECIterations << endl;
			//cout << "Total SECs Added so far =" << SECNumber << endl;
			int** RouteIsUsed;
			RouteIsUsed = new int* [kmax];
			for (k = 0; k < kmax; k++) {
				RouteIsUsed[k] = new int[rmax];
				for (r = 0; r < rmax; r++) {
					RouteIsUsed[k][r] = 0;
				}
			}
		SolveMasterAgain:;
			InfeasibleMaster = false;
			status = Solve_Master(env, modelMaster_ptr, cplexMaster_ptr, X_ijkrm, Y_ikr, Heta_k, &DTransposeY, &InfeasibleMaster);
			if (status != 0) {
				Found_Error("Solve_Master");
				return -1;
			}
			if (InfeasibleMaster == true) {
				StopTime = StopTime + StopTime;
				if (StopTime < MaxBendersDuration) {
					goto SolveMasterAgain;
				}
				else {
					break;
				}
			}
			startPrint = clock();
			status = PrintCurrentMasterSolution(loop, FilePath_Results_ptr, RouteIsUsed);
			if (status != 0) {
				Found_Error("PrintCurrentMasterSolution");
				return -1;
			}
			stopPrint = clock();
			durationPrint = durationPrint + (long double)(stopPrint - startPrint) / CLOCKS_PER_SEC;
			SubtoursExist = false;
			Sub = -1;//how many subtours are there
			NonSub = -1;//how many tours are there that are not subtours (they start and finish at the depot)
			/*for (k = 0; k < kmax; k++) {
				for (r = 0; r < rmax; r++) {
					if (RouteIsUsed[k][r] == 1) {*/
			status = DetectSubtoursInVRP(modelMaster_ptr, SubtoursNodes, NodesInSubtour, &MinNodesInSubtour, &MaxNodesInSubtour, SubtourDistance, &ShortestSubtourDistance, &Sub, &NonSub, NonSubtoursNodes, NodesInNonSubtour);
			if (status != 0) {
				Found_Error("DetectSubtoursInVRP");
				return -1;
			}

			if (Sub > 0) {
				SubtoursExist = true;
				SECIterations++;
				status = AddSECForMostDistant(env, modelMaster_ptr, FilePath_Results_ptr, Sub, SubtoursNodes, NodesInSubtour, NonSub, NonSubtoursNodes, NodesInNonSubtour, X_ijkrm, loop);
				if (status != 0) {
					Found_Error("AddSECForMostDistant");
					return -1;
				}
			}
			/*}
		}
	}*/
		}
		/*for (i = 0; i < imax + 1; i++) {
			for (j = 0; j < jmax + 1; j++) {
				cout << "NonSubtoursNodes[" << i << "][" << j << "]=" << NonSubtoursNodes[i][j] << endl;
			}
			cout << "NodesInNonSubtour[" << i << "]=" << NodesInNonSubtour[i] << endl;
		}*/
		dTy.push_back(DTransposeY);
		zCurrent.push_back(HetaValue);
		/*status = Get_Slack_Values(cplexMaster_ptr);
		if (status != 0) {
		Found_Error("Get_Slack_Values");
		return -1;
		}*/
		bool SolveFirstTime = true;

		int MultiSol = 0;
		int NodeChanged = 0;
		int* NodesVisited;
		NodesVisited = new int[kmax];
	SolveSlave:;
		for (k = 0; k < kmax; k++) {
			status = UpdateSlaveRHS(Con9_ZZZX_ijrm, Con10a_ZZY_ir, Con10b_ZZY_ir, Con11a_ZX_ijrm, Con11b_ZX_ijrm, Con12_ZZY_n, Con13_ZZY_r, Con14_ZZY_r, k);
			if (status != 0) {
				Found_Error("UpdateSlaveRHS");
				return -1;
			}

			status = Solve_Slave(env, modelSlave_ptr, cplexSlave_ptr);
			if (status != 0) {
				Found_Error("Solve_Slave");
				return -1;
			}
			NodesVisited[k] = 0;
			for (i = 0; i < imax; i++) {
				for (r = 0; r < rmax; r++) {
					NodesVisited[k] = NodesVisited[k] + Y_ikrValue[i][k][r];
				}
			}

			if (!cplexSlave_ptr.solve()) { //---------IF SLAVE1 IS INFEASIBLE-----

				status = Slave_Infeasible(env, MultiSol);
				if (status != 0) {
					Found_Error("Slave_Infeasible");
					return -1;
				}
				SlaveIsFeasible[k] = 0;//Slave is Infeasible
				status = GetExtremeRayOfDSP(cplexSlave_ptr, FeasDualValues, Con9_ZZZX_ijrm, k);
				if (status != 0) {
					Found_Error("GetExtremeRayOfDSP");
					return -1;
				}
				for (int k_prime = 0; k_prime < kmax; k_prime++) {

					IloExpr expr101(env);
					status = CreateBendersFeasCut(0, expr101, X_ijkrm, Y_ikr, Heta_k, k, k_prime);//if =0, then creates feasibility cut
					if (status != 0) {
						Found_Error("CreateBendersFeasibilityCut");
						return -1;
					}

					status = AddBendersCutToMaster(env, 0, expr101, loop, modelMaster_ptr, BendersCuts);//if =0, then adds feasibility cut
					if (status != 0) {
						Found_Error("AddBendersFeasibilityCutToMaster");
						return -1;
					}
					expr101.end();
				}

			}//Fin de IF QUI A TROUVE QUE SLAVE 1 EST INFEASIBLE

			else { //------------- IF SLAVE PROBLEM IS FEASIBLE------------
				status = Slave_Feasible(env, cplexSlave_ptr, ZZ_ir, SlaveObjFunction, k);
				if (status != 0) {
					Found_Error("Slave_Feasible");
					return -1;
				}
				SlaveIsFeasible[k] = 1;//Slave is Feasible
				bool AllAreZero = true;
				status = GetExtremePointOfDSP(cplexSlave_ptr, OptDualValues, Con9_ZZZX_ijrm, Con10a_ZZY_ir, Con10b_ZZY_ir, Con11a_ZX_ijrm, Con11b_ZX_ijrm, Con12_ZZY_n, Con13_ZZY_r, Con14_ZZY_r, k, AllAreZero);
				if (status != 0) {
					Found_Error("GetExtremePointOfDSP");
					return -1;
				}
				if (AllAreZero == false) {
					for (int k_prime = 0; k_prime < kmax; k_prime++) {

						IloExpr expr101(env);
						status = CreateBendersOptCut(1, expr101, X_ijkrm, Y_ikr, Heta_k, k, k_prime);//if =0, then creates feasibility cut
						if (status != 0) {
							Found_Error("CreateBendersFeasibilityCut");
							return -1;
						}

						status = AddBendersCutToMaster(env, 1, expr101, loop, modelMaster_ptr, BendersCuts);//if =0, then adds feasibility cut
						if (status != 0) {
							Found_Error("AddBendersFeasibilityCutToMaster");
							return -1;
						}
						expr101.end();
					}
				}

			}//end of else
		}
		AllSlavesFeasible = true;
		for (k = 0; k < kmax; k++) {
			if (SlaveIsFeasible[k] == 0) {
				AllSlavesFeasible = false;
				cTx.push_back(0);
			}
		}
		if (AllSlavesFeasible == true) {
			int NoOfRoutesUsed = 0;
			status = All_Slaves_Feasible(env, cplexSlave_ptr, &DTransposeY, &TotalSlaveObjFunction, SlaveObjFunction, &NoOfRoutesUsed, MultiSol);
			if (status != 0) {
				Found_Error("All_Slaves_Feasible");
				return -1;
			}
			//int NoOfAlternativeSolutions = round(kmax * rmax / NoOfRoutesUsed);
			//for (int NoOfOptCut = 0; NoOfOptCut < NoOfAlternativeSolutions; NoOfOptCut++) {




				//status = CreateAlternativeDualSolution(NoOfOptCut, NoOfAlternativeSolutions);//if =1sll, then creates optimality cut
				//if (status != 0) {
				//	Found_Error("CreateBendersOptimalityCut");
				//	return -1;
				//}
			//}
		}
		//if (MultiSol > 0) {
		//	if (AllSlavesFeasible == true) {
		//		MultiFeasSolutions++;
		//	}
		//	else {
		//		MultiInfeasSolutions++;
		//	}
		//}
		////GENERATE MULTIPLE SOLUTIONS
		//if (AllSlavesFeasible == false) {
		//	for (k = 0; k < kmax; k++) {
		//		if (SlaveIsFeasible[k] == 0 && MultiSol < MaxNoOfMultiSol) {//
		//			bool GeneratedNewSolution = false;
		//			status = Generate_Multiple_Solutions(MultiSol, &GeneratedNewSolution, &NodeChanged, k);
		//			if (status != 0) {
		//				Found_Error("Generate_Multiple_Solutions");
		//				return -1;
		//			}
		//			//cout << "NodeChanged= " << NodeChanged << endl;
		//			MultiSol++;
		//			if (GeneratedNewSolution == true) goto SolveSlave;
		//		}
		//	}
		//}
		//else {
		//	for (k = 0; k < kmax; k++) {
		//		if (MultiSol < MaxNoOfMultiSol) {//
		//			bool GeneratedNewSolution = false;
		//			status = Generate_Multiple_Solutions(MultiSol, &GeneratedNewSolution, &NodeChanged, k);
		//			if (status != 0) {
		//				Found_Error("Generate_Multiple_Solutions");
		//				return -1;
		//			}
		//			//cout << "NodeChanged= " << NodeChanged << endl;
		//			MultiSol++;
		//			if (GeneratedNewSolution == true) goto SolveSlave;
		//		}
		//	}
		//}

		////CHECK INFEASIBILITY OF THE AUXILIARY SUBPROBLEM

		///*SlaveIsFeasible[0] = 0;
		//DualValueCon14_ZZY_kr[0][1] = 1;
		//Y_ikrValue[3][0][1] = 1;
		//Y_ikrValue[4][0][1] = 1;
		//Y_ikrValue[15][0][1] = 1;
		//Y_ikrValue[12][0][1] = 1;
		//Y_ikrValue[14][0][1] = 1;
		//Y_ikrValue[13][0][1] = 1;
		//Y_ikrValue[9][0][1] = 1;
		//Y_ikrValue[11][0][1] = 1;
		//Y_ikrValue[10][0][1] = 1;
		//Y_ikrValue[9][0][1] = 1;
		//Y_ikrValue[5][0][1] = 0;
		//Y_ikrValue[6][0][1] = 0;
		//Y_ikrValue[2][0][1] = 0;
		//Y_ikrValue[1][0][1] = 0;
		//Y_ikrValue[7][0][1] = 0;*/




		////GENERATE 1 FEASIBLE (?) SOLUTION
		//if (SolveFirstTime == true) {
		//	bool NewSolution = false;
		//	status = Generate_Feasible_Solution(&NewSolution);
		//	if (status != 0) {
		//		Found_Error("Generate_Feasible_Solution");
		//		return -1;
		//	}
		//	if (NewSolution == true) {
		//		SolveFirstTime = false;
		//		goto SolveSlave;
		//	}
		//}

		//bool InfeasibleAuxSlave = false;
		//for (k = 0; k < kmax; k++) {
		//	if (SlaveIsFeasible[k] == 0) {//If slave is infeasible
		//		for (r = 0; r < rmax; r++) {
		//			if (DualValueCon14_ZZY_kr[k][r] != 0) {
		//				status = UpdateAuxSlaveRHS(Con2_aux_YX_n, Con3_aux_YX_n, Con4a_aux_YX_i, Con4b_aux_YX_i, Con9_aux_ZZZX_ijm, Con10a_aux_ZZY_i, Con10b_aux_ZZY_i, Con11a_aux_ZX_ijm, Con11b_aux_ZX_ijm, Con14_aux_ZZY_n, k, r);
		//				if (status != 0) {
		//					Found_Error("UpdateAuxSlaveRHS");
		//					return -1;
		//				}
		//				status = Solve_AuxSlave(env, modelAuxSlave, cplexAuxSlave_ptr, X_aux_ijm, ZZ_aux_i, &InfeasibleAuxSlave);
		//				if (status != 0) {
		//					Found_Error("Solve_AuxSlave");
		//					return -1;
		//				}
		//				if (InfeasibleAuxSlave == true) {
		//					status = CreateAddAuxFeasibilityCutToMaster(env, loop, modelMaster_ptr, Y_ikr, AuxFeasCut_kr);//if =0, then adds feasibility cut
		//					if (status != 0) {
		//						Found_Error("CreateAddAuxFeasibilityCutToMaster");
		//						return -1;
		//					}
		//				}
		//			}
		//		}
		//	}
		//}



		BestSlaveObjSoFar.push_back(OptimalSlaveObjFunction);
		LowerBoundArray.push_back(LowerBound);
		UpperBoundArray.push_back(UpperBoundOR);
		UpperBoundGlobalArray.push_back(UpperBoundGlobal);
		LowerBoundGlobalArray.push_back(LowerBoundGlobal);
		Time.push_back((long double)(clock() - start) / CLOCKS_PER_SEC);
		NoOfCutsInEachIteration.push_back(CutsPerIteration);
		Gap = (UpperBoundGlobal - LowerBoundGlobal) / UpperBoundGlobal;
		/*
		if(ThetaValue!=0){
		cout<<"OptimalThetaValue="<<OptimalThetaValue<<endl;
		}
		if(DTransposeY!=0){
		cout<<"DTransposeY="<<DTransposeY<<endl;
		}
		if(SlaveObjFunction!=0){
		cout<<"SlaveObjFunction="<<SlaveObjFunction<<endl;
		}
		if(OptimalSlaveObjFunction!=0){
		cout<<"OptimalSlaveObjFunction="<<OptimalSlaveObjFunction<<endl;
		}
		*/
		cout << "LowerBound=" << LowerBound << endl;
		cout << "LowerBoundGlobal=" << LowerBoundGlobal << endl;
		cout << "UpperBoundGlobal=" << UpperBoundGlobal << endl;
		cout << "Gap=" << Gap * 100 << "%" << endl;
		//cout<<"UpperBound="<<UpperBound<<endl;
		cout << "-----------------" << endl;
		cout << "------END OF ITERATION--------" << endl;
		/*if (Gap < 0.2) {
			Big_M = 10000;
		}*/
		if (loop > 1) {
			/*cout << "LowerBoundGlobal=" << LowerBoundGlobalArray.at(loop-1) << endl;
			cout << "UpperBoundGlobal=" << UpperBoundGlobalArray.at(loop-1) << endl;
			cout << "LowerBoundGlobal(-1)=" << LowerBoundGlobalArray.at(loop-2) << endl;
			cout << "UpperBoundGlobal(-1)=" << UpperBoundGlobalArray.at(loop-2) << endl;*/
			if (((UpperBoundGlobalArray.at(loop - 2) - LowerBoundGlobalArray.at(loop - 2)) / UpperBoundGlobalArray.at(loop - 2)) - Gap < 0.0001) {
				cout << "Gap(-1)=" << (UpperBoundGlobalArray.at(loop - 2) - LowerBoundGlobalArray.at(loop - 2)) / UpperBoundGlobalArray.at(loop - 2) << endl;
				cout << "Gap=" << Gap << endl;
				MaxNoOfMultiSol = MaxNoOfMultiSol + MaxNoOfMultiSol / 2.0;
				if (MaxNoOfMultiSol > MaxMaxNoOfMultiSol) MaxNoOfMultiSol = MaxMaxNoOfMultiSol;
				if (StopTime > MaxBendersDuration / 4.0) {
					StopTime = StopTime + StopTime / 2.0;
				}
				else {
					StopTime = StopTime + StopTime;
				}

			}
			else {
				MaxNoOfMultiSol = MinMaxNoOfMultiSol;
				//StopTime = MinStopTime;
			}
		}
		if (UpperBoundGlobal < Big_M) {
			StopTime = (MaxBendersDuration - (clock() - start) / CLOCKS_PER_SEC) / 2.0;
		}

	}//end of loop
	*loop_iter = loop;
	//cout << "loop_iter=" << *loop_iter << endl;
	return 0;
}//end of BendersIteration
int PrintData(char* FilePath_Results_ptr) {
	int status, test = 0;
	char* FileName_ptr;
	char filepath[1024];
	char FileName_Problem_ptr[6];
	if (FileName_Problem[1] == 'c') {
		memcpy(FileName_Problem_ptr, &FileName_Problem[0], 5);
		FileName_Problem_ptr[5] = '\0';
	}
	else {
		memcpy(FileName_Problem_ptr, &FileName_Problem[0], 4);
		FileName_Problem_ptr[4] = '\0';
	}
	cout << FileName_Problem_ptr << endl;
	sprintf(filepath, "%s/%s", FilePath_Results_ptr, FileName_Problem_ptr);
	//string stringpath = filepath;
	status = mkdir(filepath);
	sprintf(filepath, "%s/%s/DATA", FilePath_Results_ptr, FileName_Problem_ptr);
	//string stringpath = filepath;
	status = mkdir(filepath);
	sprintf(filepath, "%s/%s/DATA/%s_DATA_CustomersData.txt", FilePath_Results_ptr, FileName_Problem_ptr, FileName_Problem_ptr);
	outfile.open(filepath);
	for (int i = 0; i < imax + 1; i++) {
		outfile << i << '\t';
		outfile << XCOORD_i[i] << '\t';
		outfile << YCOORD_i[i] << '\t';
		outfile << q_i[i] << '\t';
		outfile << e_i[i] << '\t';
		outfile << l_i[i] << '\t';
		outfile << s_i[i] << endl;
	}
	outfile.close();

	sprintf(filepath, "%s/%s/DATA/%s_DATA_DistanceMatrix.txt", FilePath_Results_ptr, FileName_Problem_ptr, FileName_Problem_ptr);
	outfile.open(filepath);
	for (int i = 0; i < imax + 1; i++) {
		for (int j = 0; j < jmax + 1; j++) {
			outfile << Distance_ij[i][j] << '\t';
		}
		outfile << std::endl;
	}
	outfile.close();

	sprintf(filepath, "%s/%s/DATA/%s_DATA_EdgeCategory.txt", FilePath_Results_ptr, FileName_Problem_ptr, FileName_Problem_ptr);
	outfile.open(filepath);
	for (int i = 0; i < imax + 1; i++) {
		for (int j = 0; j < jmax + 1; j++) {
			outfile << EdgeCat_ij[i][j] << '\t';
		}
		outfile << std::endl;
	}
	outfile.close();

	sprintf(filepath, "%s/%s/DATA/%s_DATA_SpeedCategoryOverTime.txt", FilePath_Results_ptr, FileName_Problem_ptr, FileName_Problem_ptr);
	outfile.open(filepath);
	for (int p = 0; p < pmax; p++) {
		for (int c = 0; c < cmax; c++) {
			outfile << SpeedOfCatOverTime_p_c[p][c] << '\t';
		}
		outfile << std::endl;
	}
	outfile.close();

	sprintf(filepath, "%s/%s/DATA/%s_DATA_TravelTimeBreakpoints.txt", FilePath_Results_ptr, FileName_Problem_ptr, FileName_Problem_ptr);
	outfile.open(filepath);
	for (int i = 0; i < imax + 1; i++) {
		for (int j = 0; j < jmax + 1; j++) {
			for (int m = 0; m < mmax; m++) {
				outfile << w_ijm[i][j][m] << '\t';
			}
			outfile << std::endl;
		}
		outfile << std::endl;
		outfile << std::endl;
	}
	outfile.close();

	sprintf(filepath, "%s/%s/DATA/%s_DATA_TravelTimeBreakpointsMinMax.txt", FilePath_Results_ptr, FileName_Problem_ptr, FileName_Problem_ptr);
	outfile.open(filepath);
	for (int m = 0; m < mmax; m++) {
		outfile << w_max_m[m] << '\t';
	}
	outfile << std::endl;
	for (int m = 0; m < mmax; m++) {
		outfile << w_min_m[m] << '\t';
	}
	outfile.close();


	sprintf(filepath, "%s/%s/DATA/%s_DATA_TravelTime.txt", FilePath_Results_ptr, FileName_Problem_ptr, FileName_Problem_ptr);
	outfile.open(filepath);
	for (int i = 0; i < imax + 1; i++) {
		for (int j = 0; j < jmax + 1; j++) {
			for (int m = 0; m < mmax; m++) {
				outfile << TravelTime_ijm[i][j][m] << '\t';
			}
			outfile << std::endl;
		}
		outfile << std::endl;
		outfile << std::endl;
	}
	outfile.close();

	sprintf(filepath, "%s/%s/DATA/%s_DATA_TravelTimeCalculated.txt", FilePath_Results_ptr, FileName_Problem_ptr, FileName_Problem_ptr);
	outfile.open(filepath);
	for (int i = 0; i < imax + 1; i++) {
		for (int j = 0; j < jmax + 1; j++) {
			for (int m = 0; m < mmax; m++) {
				outfile << TravelTimeCalculated_ijm[i][j][m] << '\t';
			}
			outfile << std::endl;
		}
		outfile << std::endl;
		outfile << std::endl;
	}
	outfile.close();

	sprintf(filepath, "%s/%s/DATA/%s_DATA_TravelTimeAverage.txt", FilePath_Results_ptr, FileName_Problem_ptr, FileName_Problem_ptr);
	outfile.open(filepath);
	for (int i = 0; i < imax + 1; i++) {
		for (int j = 0; j < jmax + 1; j++) {
			for (int m = 0; m < mmax; m++) {
				outfile << TravelTimeAverage_ijm[i][j][m] << '\t';
			}
			outfile << std::endl;
		}
		outfile << std::endl;
		outfile << std::endl;
	}
	outfile.close();

	sprintf(filepath, "%s/%s/DATA/%s_DATA_TravelTimeMinimum_ijm.txt", FilePath_Results_ptr, FileName_Problem_ptr, FileName_Problem_ptr);
	outfile.open(filepath);
	for (int i = 0; i < imax + 1; i++) {
		for (int j = 0; j < jmax + 1; j++) {
			for (int m = 0; m < mmax; m++) {
				outfile << TravelTimeMinimum_ijm[i][j][m] << '\t';
			}
			outfile << std::endl;
		}
		outfile << std::endl;
		outfile << std::endl;
	}
	outfile.close();

	sprintf(filepath, "%s/%s/DATA/%s_DATA_TravelTimeMinimum_ij.txt", FilePath_Results_ptr, FileName_Problem_ptr, FileName_Problem_ptr);
	outfile.open(filepath);
	for (int i = 0; i < imax + 1; i++) {
		for (int j = 0; j < jmax + 1; j++) {
			outfile << TravelTimeMinimum_ij[i][j] << '\t';
		}
		outfile << std::endl;
	}
	outfile.close();

	sprintf(filepath, "%s/%s/DATA/%s_DATA_Theta.txt", FilePath_Results_ptr, FileName_Problem_ptr, FileName_Problem_ptr);
	outfile.open(filepath);
	for (int i = 0; i < imax + 1; i++) {
		for (int j = 0; j < jmax + 1; j++) {
			for (int m = 0; m < mmax; m++) {
				outfile << theta_ijm[i][j][m] << '\t';
			}
			outfile << std::endl;
		}
		outfile << std::endl;
		outfile << std::endl;
	}
	outfile.close();

	sprintf(filepath, "%s/%s/DATA/%s_DATA_Zeta.txt", FilePath_Results_ptr, FileName_Problem_ptr, FileName_Problem_ptr);
	outfile.open(filepath);
	for (int i = 0; i < imax + 1; i++) {
		for (int j = 0; j < jmax + 1; j++) {
			for (int m = 0; m < mmax; m++) {
				outfile << zeta_ijm[i][j][m] << '\t';
			}
			outfile << std::endl;
		}
		outfile << std::endl;
		outfile << std::endl;
	}
	outfile.close();

	return 0;
}
int PrintOptimalSolution(char* FilePath_Results_ptr, int loop_iter) {
	int status, test = 0;
	char* FileName_ptr;
	char filepath[1024];
	char FileName_Problem_ptr[6];
	if (FileName_Problem[1] == 'c') {
		memcpy(FileName_Problem_ptr, &FileName_Problem[0], 5);
		FileName_Problem_ptr[5] = '\0';
	}
	else {
		memcpy(FileName_Problem_ptr, &FileName_Problem[0], 4);
		FileName_Problem_ptr[4] = '\0';
	}
	//cout << FileName_Problem_ptr << endl;
	sprintf(filepath, "%s/%s", FilePath_Results_ptr, FileName_Problem_ptr);
	//string stringpath = filepath;
	status = mkdir(filepath);
	sprintf(filepath, "%s/%s/%s_BENDERS_OptimalSolution.txt", FilePath_Results_ptr, FileName_Problem_ptr, FileName_Problem_ptr);
	outfile.open(filepath);

	/*

		std::ostringstream os;
		os << "D:\\Antonis\\PhD_Examples\\Results_WWTN\\BENDERS\\OptimalSolution.txt";
		std::string FileName = os.str();

		std::ofstream fsOptimalSolution;
		fsOptimalSolution.open(FileName.c_str(), std::ios::out);*/
	outfile << FileName_Problem_ptr << std::endl;
	outfile << "Running time: " << duration << " seconds " << std::endl;
	outfile << "Optimality Gap= " << Gap << std::endl;
	outfile << "Optimal ObjFunction= " << OptimalOriginalObjFunction << std::endl;
	if (Gap < epsilon)SolutionStatus = 2;//Optimal
	outfile << "Solution Status= " << SolutionStatus << std::endl;
	outfile << "Total BendersIterations= " << loop_iter << std::endl;
	outfile << "TotalNumberOf FeasibilityCuts= " << BDFeasCuts << std::endl;
	outfile << "TotalNumberOf OptimalityCuts= " << BDOptCuts << std::endl;
	outfile << "TotalNumberOf AuxiliaryFeasibilityCuts= " << AuxFeasCuts << std::endl;
	outfile << "Multi InfeasibleSolutions= " << MultiInfeasSolutions << endl;
	outfile << "Multi FeasibleSolutions= " << MultiFeasSolutions << endl;
	outfile << "MasterProblem StopTime= " << StopTime << endl;
	outfile << "MaxMultipleSolutions PerIteration= " << MaxNoOfMultiSol << endl;
	outfile << "SEC Iterations= " << SECIterations << endl;
	outfile << "TotalSECs Added= " << SECNumber << endl;
	outfile << "Optimal MasterObjFunction= " << OptimalMasterObjFunction << std::endl;
	outfile << "Optimal SlaveObjFunction= " << OptimalSlaveObjFunction << std::endl;
	outfile << "----------------------------------" << std::endl;
	if (OptimalHetaValue > 0.01) {
		outfile << "Optimal HetaValue= " << OptimalHetaValue << std::endl;
	}
	outfile << "----------------------------------" << std::endl;
	outfile << "TotalNumberOf MasterVariables= " << NoOfMasterVars << std::endl;
	outfile << "TotalNumberOf SlaveVariables= " << NoOfSlaveVars << std::endl;
	outfile << "TotalNumberOf MasterConstraints= " << NoOfMasterCons << std::endl;
	outfile << "TotalNumberOf SlaveConstraints= " << NoOfSlaveCons << std::endl;
	if (SolutionStatus != 0) {
		for (k = 0; k < kmax; k++) {
			for (r = 0; r < rmax; r++) {
				outfile << "Veh - Trip:" << k << "	" << r << endl;
				for (m = 0; m < mmax; m++) {
					for (i = 0; i < 1; i++) {
						for (j = 1; j < jmax + 1; j++) {
							if (OptimalX_ijkrmValue[i][j][k][r][m] > 0.9) {
								test = j;
								//distance = distance + Distance_ij[i][j];
								outfile << i << "	" << OptimalZZ_ikrValue[i][k][r] << endl;
								outfile << j << "	" << OptimalZZ_ikrValue[j][k][r] << endl;
								goto Restart2;
							}
						}
					}
				}
			Restart2:;
				for (m = 0; m < mmax; m++) {
					for (i = 0; i < imax; i++) {
						if (test != 0) {
							if (i == test) {
								for (j = 0; j < jmax + 1; j++) {
									if (OptimalX_ijkrmValue[i][j][k][r][m] > 0.9) {
										test = j;
										//distance = distance + Distance_ij[i][j];
										outfile << j << "	" << OptimalZZ_ikrValue[j][k][r] << endl;
										/*if (test == jmax) {
											outfile << j << "	" << ZZ_ikrValue[imax][k][r] << endl;
										}*/
										i = 0;
										goto Restart2;
									}
								}
							}
						}
						else break;
					}

				}
				outfile << endl;
			}
		}
	}
	outfile.close();

	sprintf(filepath, "%s/%s/%s_BENDERS_Variables.txt", FilePath_Results_ptr, FileName_Problem_ptr, FileName_Problem_ptr);
	outfile.open(filepath);
	for (k = 0; k < kmax; k++) {
		for (r = 0; r < rmax; r++) {
			for (i = 0; i < imax + 1; i++) {
				for (j = 0; j < jmax + 1; j++) {
					for (m = 0; m < mmax; m++) {
						if (OptimalX_ijkrmValue[i][j][k][r][m] >= 0.01) outfile << "X_ijkrm[" << i << "][" << j << "][" << k << "][" << r << "][" << m << "]=" << OptimalX_ijkrmValue[i][j][k][r][m] << endl;
					}
				}
			}
		}
	}
	outfile << "----------------------------------" << std::endl;
	for (i = 0; i < imax + 1; i++) {
		for (k = 0; k < kmax; k++) {
			for (r = 0; r < rmax; r++) {
				if (OptimalY_ikrValue[i][k][r] >= 0.01) outfile << "Y_ikr[" << i << "][" << k << "][" << r << "]=" << OptimalY_ikrValue[i][k][r] << endl;
			}
		}
	}
	outfile << "----------------------------------" << std::endl;
	for (k = 0; k < kmax; k++) {
		for (r = 0; r < rmax; r++) {
			for (i = 0; i < imax + 1; i++) {
				if (OptimalZZ_ikrValue[i][k][r] >= 0.01) outfile << "ZZ_ikr[" << i << "][" << k << "][" << r << "]=" << OptimalZZ_ikrValue[i][k][r] << endl;
			}
		}
	}
	outfile << "----------------------------------" << std::endl;
	/*for (k = 0; k < kmax; k++) {
		for (r = 0; r < rmax; r++) {
			for (i = 0; i < imax + 1; i++) {
				for (j = 0; j < jmax + 1; j++) {
					for (m = 0; m < mmax; m++) {
						if (Z_ijkrmValue[i][j][k][r][m] >= 0.01) outfile << "Z_ijkrm[" << i << "][" << j << "][" << k << "][" << r << "][" << m << "]=" << Z_ijkrmValue[i][j][k][r][m] << endl;
					}
				}
			}
		}
	}*/
	outfile.close();


	//sprintf(filepath, "%s/%s/%s_BENDERS_TimeSpent.txt", FilePath_Results_ptr, FileName_Problem_ptr, FileName_Problem_ptr);
	//outfile.open(filepath);
	//outfile << MasterTime / duration << std::endl;
	//for (i = 0; i < NumberOfProblems; i++) {
	//	outfile << SlaveTime[i] / duration << std::endl;
	//}
	//outfile.close();

	sprintf(filepath, "%s/%s/%s_BENDERS_LowerBound.txt", FilePath_Results_ptr, FileName_Problem_ptr, FileName_Problem_ptr);
	outfile.open(filepath);
	for (i = 0; i < LowerBoundArray.size(); i++) {
		outfile << LowerBoundArray.at(i) << std::endl;
	}
	outfile.close();

	sprintf(filepath, "%s/%s/%s_BENDERS_UpperBound.txt", FilePath_Results_ptr, FileName_Problem_ptr, FileName_Problem_ptr);
	outfile.open(filepath);
	for (i = 0; i < UpperBoundArray.size(); i++) {
		outfile << UpperBoundArray.at(i) << std::endl;
	}
	outfile.close();

	sprintf(filepath, "%s/%s/%s_BENDERS_UpperBoundGlobal.txt", FilePath_Results_ptr, FileName_Problem_ptr, FileName_Problem_ptr);
	outfile.open(filepath);
	for (i = 0; i < UpperBoundGlobalArray.size(); i++) {
		outfile << UpperBoundGlobalArray.at(i) << std::endl;
	}
	outfile.close();

	sprintf(filepath, "%s/%s/%s_BENDERS_LowerBoundGlobal.txt", FilePath_Results_ptr, FileName_Problem_ptr, FileName_Problem_ptr);
	outfile.open(filepath);
	for (i = 0; i < LowerBoundGlobalArray.size(); i++) {
		outfile << LowerBoundGlobalArray.at(i) << std::endl;
	}
	outfile.close();

	sprintf(filepath, "%s/%s/%s_BENDERS_dTransY.txt", FilePath_Results_ptr, FileName_Problem_ptr, FileName_Problem_ptr);
	outfile.open(filepath);
	for (i = 0; i < dTy.size(); i++) {
		outfile << dTy.at(i) << std::endl;
	}
	outfile.close();

	sprintf(filepath, "%s/%s/%s_BENDERS_cTransX.txt", FilePath_Results_ptr, FileName_Problem_ptr, FileName_Problem_ptr);
	outfile.open(filepath);
	for (i = 0; i < cTx.size(); i++) {
		outfile << cTx.at(i) << std::endl;
	}
	outfile.close();

	sprintf(filepath, "%s/%s/%s_BENDERS_CurrentHeta.txt", FilePath_Results_ptr, FileName_Problem_ptr, FileName_Problem_ptr);
	outfile.open(filepath);
	for (i = 0; i < zCurrent.size(); i++) {
		outfile << zCurrent.at(i) << std::endl;
	}
	outfile.close();

	sprintf(filepath, "%s/%s/%s_BENDERS_BestSlaveObj.txt", FilePath_Results_ptr, FileName_Problem_ptr, FileName_Problem_ptr);
	outfile.open(filepath);
	for (i = 0; i < BestSlaveObjSoFar.size(); i++) {
		outfile << BestSlaveObjSoFar.at(i) << std::endl;
	}
	outfile.close();

	sprintf(filepath, "%s/%s/%s_BENDERS_TimePath.txt", FilePath_Results_ptr, FileName_Problem_ptr, FileName_Problem_ptr);
	outfile.open(filepath);
	for (i = 0; i < Time.size(); i++) {
		outfile << Time.at(i) << std::endl;
	}
	outfile.close();

	return 0;
}
int main(int argc, char** argv)
{
	int  stop, status;
	bool InfeasibleMaster = false;
	status = InsertDataSet(FilePath_DataSet);
	if (status != 0) {
		Found_Error("InsertDataSet");
		return -1;
	}
	for (int i_Problem = 7; i_Problem < 8; i_Problem++) {
		//if (i_Problem >= 8 && i_Problem <= 8) {//if (i_Problem == 20 || i_Problem == 24 || i_Problem == 26) {
		strcpy(FileName_Problem, ProblemNames[i_Problem].c_str());
		cout << "-------------------" << endl;
		cout << "Solving DataSet: " << FileName_Problem << endl;
		cout << "-------------------" << endl;
		//--------Declare the environment of CPLEX----------------
		IloEnv env;
		try {
			//--------Construct models----------------
			IloModel modelSlave(env);
			IloModel modelMaster(env);
			IloModel modelAuxSlave(env);

			//------Declare Master Decision Variables----------
			IloNumVarMatrix5x5 X_ijkrm(env, 0);//equal to 1 if and only if vehicle k leaves node i toward node j during time interval m in the r - th trip
			IloNumVarMatrix3x3 Y_ikr(env, 0);//equal to 1 if and only if a vehicle visits node i in the r-th trip
			//IloNumVarMatrix5x5 Z_ijkrm(env, 0); //departure time of the r-th trip by vehicle k from node i toward node j in time interval m
			IloNumVarMatrix3x3 U_ikr(env, 0);//equal to 1 if and only if a vehicle visits node i in the r-th trip
			//IloNumVarMatrix5x5 Z_ijkrm(env, 0); //departure time of the r-th trip by vehicle k from node i toward node j in time interval m
			IloNumVarMatrix2x2 ZZ_ir(env, 0);//departure time of the r-th trip by vehicle k from node i ∈ V+ or arrival time of the r - th trip by vehicle k at node n + 1
			IloNumVarArray Heta_k(env, 0);//continuous variable that takes the value of the expansion needed to be made at WWTP at location j in terms of additional amount of waste water that can be treated in it.

			//------Declare Slave Decision Variables----------


			//--------Declare Master constraints-------------
			IloRangeMatrix2x2 Con2_YX_kr(env, 0);
			IloRangeMatrix2x2 Con3_YX_kr(env, 0);
			IloRangeMatrix3x3 Con4a_YX_ikr(env, 0);
			IloRangeMatrix3x3 Con4b_YX_ikr(env, 0);
			IloRangeArray Con5_Y_i(env, 0);
			IloRangeMatrix2x2 Con6_Y_kr(env, 0);
			IloRangeMatrix3x3 Con7_ZZZ_ikr(env, 0);
			IloRangeMatrix2x2 Con8_ZZZ_kr(env, 0);
			IloRangeMatrix4x4 Con9_ZZZX_ijrm(env, 0);
			IloRangeMatrix2x2 Con10a_ZZY_ir(env, 0);
			IloRangeMatrix2x2 Con10b_ZZY_ir(env, 0);
			IloRangeMatrix4x4 Con11a_ZX_ijrm(env, 0);
			IloRangeMatrix4x4 Con11b_ZX_ijrm(env, 0);
			IloRangeArray Con12_ZZY_n(env, 0);
			IloRangeArray Con13_ZZY_r(env, 0);
			IloRangeArray Con14_ZZY_r(env, 0);
			IloRangeMatrix4x4 Con15_XX_ikrm(env, 0);
			IloRangeMatrix5x5 Con16_X_ijkrm(env, 0);
			IloRangeMatrix3x3 Con17_XX_krm(env, 0);
			IloRangeMatrix2x2 Con18_Y_kr(env, 0);
			IloRangeMatrix2x2 Con19_Y_kr(env, 0);
			IloRangeMatrix2x2 Con20_X_kr(env, 0);
			IloRangeMatrix3x3 Con20a_XX_krm(env, 0);
			IloRangeMatrix3x3 Con21_XX_ikr(env, 0);
			IloRangeMatrix3x3 Con22_X_ijm(env, 0);
			IloRangeMatrix3x3 Con23_Xw_krm(env, 0);
			IloRangeArray Con24_hX_n(env, 0);
			IloRangeArray Con24a_hX_m(env, 0);
			IloRangeArray Con25_hX_n(env, 0);
			IloRangeMatrix4x4 Con26_YY_ijkr(env, 0);
			IloRangeArray Con27_hX_n(env, 0);
			IloRangeMatrix2x2 Con28_Y_kr(env, 0);
			IloRangeMatrix4x4 Con29_XX_ijkr(env, 0);
			IloRangeMatrix5x5 Con30_XXX_ijlkr(env, 0);
			IloRangeMatrix4x4 Con31_XX_ijlm(env, 0);
			IloRangeMatrix2x2 Con32_XY_kr(env, 0);
			IloRangeArray ConAuxiliary_i(env, 0);
			IloRangeMatrix4x4 ConSEC_ijkr(env, 0);
			IloRangeArray ConAuxiliary2_n(env, 0);

			//--------Declare Variables of Auxiliary Slave Problem-------------
			IloNumVarMatrix3x3 X_aux_ijm(env, 0);
			IloNumVarArray ZZ_aux_i(env, 0);
			//--------Declare Constraints of Auxiliary Slave Problem-------------
			IloRangeArray Con2_aux_YX_n(env, 0);
			IloRangeArray Con3_aux_YX_n(env, 0);
			IloRangeArray Con4a_aux_YX_i(env, 0);
			IloRangeArray Con4b_aux_YX_i(env, 0);
			IloRangeMatrix3x3 Con9_aux_ZZZX_ijm(env, 0);
			IloRangeArray Con10a_aux_ZZY_i(env, 0);
			IloRangeArray Con10b_aux_ZZY_i(env, 0);
			IloRangeMatrix3x3 Con11a_aux_ZX_ijm(env, 0);
			IloRangeMatrix3x3 Con11b_aux_ZX_ijm(env, 0);
			IloRangeArray Con14_aux_ZZY_n(env, 0);

			//--------Declare Array of Benders Cuts Added in Master Problem-------------
			IloRangeArray BendersCuts(env, 0);
			IloRangeMatrix2x2 AuxFeasCut_kr(env, 0);
			IloNum OptDualValues;
			IloNumArray FeasDualValues(env, 0);
			IloNumArray SlackValues(env, 0);
			//IloNum SlackValuesMasterCons;

			//--------Declare Slave constraints-------------
			cout << "Loading Data..." << endl;
			status = load_data(FilePath_Data);
			if (status != 0) {
				Found_Error("load_data");
				return -1;
			}
			status = PrintData(FilePath_Results);
			if (status != 0) {
				Found_Error("PrintData");
				return -1;
			}
			durationPrint = 0;
			start = clock();
			auto TimeNow = std::chrono::system_clock::now();
			std::time_t CurTime = std::chrono::system_clock::to_time_t(TimeNow);
			std::cout << "Started at " << std::ctime(&CurTime);
			cout << "Building Master Model..." << endl;

			status = do_master(env, modelMaster, X_ijkrm, Y_ikr, U_ikr, Heta_k, Con2_YX_kr, Con3_YX_kr, Con4a_YX_ikr, Con4b_YX_ikr, Con5_Y_i, Con6_Y_kr, Con15_XX_ikrm, Con16_X_ijkrm, Con17_XX_krm, Con18_Y_kr, Con19_Y_kr, Con20_X_kr, Con20a_XX_krm, Con21_XX_ikr, Con22_X_ijm, Con23_Xw_krm, Con24_hX_n, Con24a_hX_m, Con25_hX_n, Con26_YY_ijkr, Con27_hX_n, Con28_Y_kr, Con29_XX_ijkr, Con30_XXX_ijlkr, Con31_XX_ijlm, Con32_XY_kr, ConAuxiliary_i, ConSEC_ijkr, ConAuxiliary2_n);
			if (status != 0) {
				Found_Error("do_master");
				return -1;
			}
			cout << "Building Slave Model..." << endl;
			status = do_slave(env, modelSlave, ZZ_ir, Con9_ZZZX_ijrm, Con10a_ZZY_ir, Con10b_ZZY_ir, Con11a_ZX_ijrm, Con11b_ZX_ijrm, Con12_ZZY_n, Con13_ZZY_r, Con14_ZZY_r);
			if (status != 0) {
				Found_Error("do_slave");
				return -1;
			}
			status = do_aux_slave(env, modelAuxSlave, X_aux_ijm, ZZ_aux_i, Con2_aux_YX_n, Con3_aux_YX_n, Con4a_aux_YX_i, Con4b_aux_YX_i, Con9_aux_ZZZX_ijm, Con10a_aux_ZZY_i, Con10b_aux_ZZY_i, Con11a_aux_ZX_ijm, Con11b_aux_ZX_ijm, Con14_aux_ZZY_n);
			if (status != 0) {
				Found_Error("do_aux_slave");
				return -1;
			}
			OptDualValues = 0;
			int loop_iter = 0;
			cout << "Applying Benders Algorithm..." << endl;
			status = BendersIteration(env, modelMaster, modelSlave, X_ijkrm, Y_ikr, Heta_k, Con2_YX_kr, Con3_YX_kr, Con4a_YX_ikr, Con4b_YX_ikr, Con5_Y_i, Con6_Y_kr, Con15_XX_ikrm, Con16_X_ijkrm, ConAuxiliary_i, ZZ_ir, Con9_ZZZX_ijrm, Con10a_ZZY_ir, Con10b_ZZY_ir, Con11a_ZX_ijrm, Con11b_ZX_ijrm, Con12_ZZY_n, Con13_ZZY_r, Con14_ZZY_r, BendersCuts, OptDualValues, FeasDualValues, FilePath_Results, &loop_iter, modelAuxSlave, X_aux_ijm, ZZ_aux_i, Con2_aux_YX_n, Con3_aux_YX_n, Con4a_aux_YX_i, Con4b_aux_YX_i, Con9_aux_ZZZX_ijm, Con10a_aux_ZZY_i, Con10b_aux_ZZY_i, Con11a_aux_ZX_ijm, Con11b_aux_ZX_ijm, Con14_aux_ZZY_n, AuxFeasCut_kr);
			if (status != 0) {
				Found_Error("BendersIteration");
				return -1;
			}
			stop = clock();
			duration = (long double)(stop - start) / CLOCKS_PER_SEC;
			duration = duration - durationPrint;
			cout << "Printing solution..." << endl;
			status = PrintOptimalSolution(FilePath_Results, loop_iter);
			if (status != 0) {
				Found_Error("PrintOptimalSolution");
				return -1;
			}
		}
		catch (IloException& e) {
			cout << "Error : " << e << endl;
		}
		env.end();
		printf("Code terminated successfully \n");
		//cout << "UpperBoundGlobal=" << UpperBoundGlobal << endl;
		printf("Execution time = %Lf seconds\n", duration);
		printf("Printing time = % Lf seconds\n", durationPrint);
		printf("MultiInfeasSolutions = % d \n", MultiInfeasSolutions);
		printf("MultiFeasSolutions = % d \n", MultiFeasSolutions);
		//	}
	}
	return 0;

} //End main
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
int i, j, k, r, m, c, p; //indices
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
double*** TravelTime_ijm;//travel time at the m-th time intervals based on distance/speed
double*** TravelTimeCalculated_ijm;//calculated travel time at the m-th time intervals based on theta and zeta
float*** theta_ijm;//slope of travel time function between i and j in m-th breakpoint
float*** zeta_ijm;//intersection with y-axis of travel time function between i and j in m-th breakpoint




//Parameters affecting solution
double epsilon = 0.1;
int Big_M = 1000000;
double UpperBound = Big_M;
double LowerBound = -Big_M;
double UpperBoundGlobal = Big_M;
double Gap = 1;
int SolutionStatus;
double StopGapMaster = 0;//Optimality Gap to stop the code
double StopTime = 1800;//Seconds to stop the code
double fraction = 0.90;
long double duration;  // tracks time
int start = 0, BDFeasCuts = 0, BDOptCuts = 0, CutsPerIteration, NoOfMasterVars, NoOfSlaveVars, NoOfMasterCons, NoOfSlaveCons;

ifstream infile;
ofstream outfile, solution, solution_results, solution1, solution_results1;
char* FilePath_DataSet = "G:/Antonis/PhD_Examples/MT-TDVRPTW/MT-TDVRPTW-Small/";
char* FilePath_Data = "G:/Antonis/PhD_Examples/MT-TDVRPTW/MT-TDVRPTW-Small/T15-5-2";
char* FilePath_Results = "G:/Antonis/PhD_Examples/MT-TDVRPTW/MT-TDVRPTWResults-Small/T15-5-2/CPLEX_2";//G:/Antonis/PhD_Examples
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


//--------Declare Array of Benders Cuts Added in Master Problem-------------
//IloRangeArray BendersCuts(env, 0);

//--------Declare dual variables of each constraint----------------
//double DualValueCon1_Z_i[imax];
//double DualValueCon2_Z_j[jmax];
//double DualValueCon3_Z_ij[imax][jmax];
//double DualValueCon5_Q_j[jmax];
//double DualValueCon6_R_j[jmax];
//double DualValueCon7_R_j[jmax];
//double DualValueCon8_WQ_j[jmax];
//double DualValueCon9_WR_j[jmax];
//double DualValueCon10_WQ_j[jmax];
//double DualValueCon11_WR_j[jmax];
//double DualValueCon12_int_WQ_jb[jmax][bmax];
//double DualValueCon13_int_WR_jb[jmax][bmax];
//double DualValueCon18_int_WQ_jb[jmax][bmax];
//double DualValueCon19_int_WR_jb[jmax][bmax];

//------Declare empty arrays that will host the optimal solution------
double***** X_ijkrmValue;
double*** Y_ikrValue;
double*** ZZ_ikrValue;
//double***** Z_ijkrmValue;

//double ThetaValue = 0;
double***** OptimalX_ijkrmValue;
double*** OptimalY_jkrValue;
double*** OptimalZZ_ikrValue;
//double***** OptimalZ_ijkrmValue;

//double OptimalThetaValue = 0;

double OptimalOriginalObjFunction = 0;
//double OptimalMasterObjFunction = 0;
//double OptimalSlaveObjFunction = 0;

//----------What does IloNum mean?---------------

//IloNum OptDualValues;
//IloNumArray FeasDualValues(env, 0);
//IloNumArray SlackValues(env, 0);
//IloNum SlackValuesMasterCons;

//vector <double> LowerBoundArray;
//vector <double> UpperBoundArray;
//vector <double> UpperBoundGlobalArray;
//vector <double> dTy;
//vector <double> zCurrent;
//vector <double> cTx;
//vector <double> BestSlaveObjSoFar;
//vector <double> Time;
//vector <double> SlackValuesOfBendersCuts;
//vector <double> SlackValuesOfMainMasterCons;
//vector <double> NoOfCutsInEachIteration;
//vector <double> NoOfCoveredVarsInEachIteration;

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
	for (i = 0; i < imax_plus; i++) {
		EdgeCat_ij[i] = new int[jmax_plus];
		Distance_ij[i] = new double[jmax_plus];
	}
	Speed_ijp = new double** [imax_plus];
	w_ijm = new double** [imax_plus];
	TravelTime_ijm = new double** [imax_plus];
	TravelTimeCalculated_ijm = new double** [imax_plus];
	theta_ijm = new float** [imax_plus];
	zeta_ijm = new float** [imax_plus];
	for (i = 0; i < imax_plus; i++) {
		Speed_ijp[i] = new double* [jmax_plus];
		w_ijm[i] = new double* [jmax_plus];
		TravelTime_ijm[i] = new double* [jmax_plus];
		TravelTimeCalculated_ijm[i] = new double* [jmax_plus];
		theta_ijm[i] = new float* [jmax_plus];
		zeta_ijm[i] = new float* [jmax_plus];
	}
	for (i = 0; i < imax_plus; i++) {
		for (j = 0; j < jmax_plus; j++) {
			Speed_ijp[i][j] = new double[pmax];
			w_ijm[i][j] = new double[mmax];
			TravelTime_ijm[i][j] = new double[mmax];
			TravelTimeCalculated_ijm[i][j] = new double[mmax];
			theta_ijm[i][j] = new float[mmax];
			zeta_ijm[i][j] = new float[mmax];
		}
	}

	X_ijkrmValue = new double**** [imax_plus];
	//Z_ijkrmValue = new double****[imax_plus];
	Y_ikrValue = new double** [imax_plus];
	ZZ_ikrValue = new double** [imax_plus];
	for (i = 0; i < imax_plus; i++) {
		X_ijkrmValue[i] = new double*** [jmax_plus];
		//Z_ijkrmValue[i] = new double***[jmax_plus];
		Y_ikrValue[i] = new double* [kmax];
		ZZ_ikrValue[i] = new double* [kmax];
	}
	for (i = 0; i < imax_plus; i++) {
		for (j = 0; j < jmax_plus; j++) {
			X_ijkrmValue[i][j] = new double** [kmax];
			//Z_ijkrmValue[i][j] = new double**[kmax];
		}
		for (k = 0; k < kmax; k++) {
			Y_ikrValue[i][k] = new double[rmax];
			ZZ_ikrValue[i][k] = new double[rmax];
		}
	}

	for (i = 0; i < imax_plus; i++) {
		for (j = 0; j < jmax_plus; j++) {
			for (k = 0; k < kmax; k++) {
				X_ijkrmValue[i][j][k] = new double* [rmax];
				//Z_ijkrmValue[i][j][k] = new double*[rmax];
			}
		}
	}
	for (i = 0; i < imax_plus; i++) {
		for (j = 0; j < jmax_plus; j++) {
			for (k = 0; k < kmax; k++) {
				for (r = 0; r < rmax; r++) {
					X_ijkrmValue[i][j][k][r] = new double[mmax];
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
			for (m = 0; m < mmax; m++) {
				TravelTimeCalculated_ijm[i][j][m] = theta_ijm[i][j][m] * w_ijm[i][j][m] + zeta_ijm[i][j][m];
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
	FileName_ptr = "instructions.txt";
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
int do_master(IloEnv env, IloModel modelMaster, IloNumVarMatrix5x5 X_ijkrm, IloNumVarMatrix3x3 Y_ikr, IloNumVarMatrix3x3 ZZ_ikr, IloRangeMatrix2x2 Con2_YX_kr, IloRangeMatrix2x2 Con3_YX_kr, IloRangeMatrix3x3 Con4a_YX_ikr, IloRangeMatrix3x3 Con4b_YX_ikr, IloRangeArray Con5_Y_i, IloRangeMatrix2x2 Con6_Y_kr, IloRangeMatrix3x3 Con7_ZZZ_ikr, IloRangeMatrix2x2 Con8_ZZZ_kr, IloRangeMatrix5x5 Con9_ZZZX_ijkrm, IloRangeMatrix3x3 Con10a_ZZY_ikr, IloRangeMatrix3x3 Con10b_ZZY_ikr, IloRangeMatrix5x5 Con11a_ZX_ijkrm, IloRangeMatrix5x5 Con11b_ZX_ijkrm, IloRangeArray Con12_ZZY_k, IloRangeMatrix2x2 Con13_ZZY_kr, IloRangeMatrix2x2 Con14_ZZY_kr, IloRangeArray ConAuxiliary_i) {

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
	//-------------- Decision Variable ZZ_ikr ---------------------------------------
	for (i = 0; i < imax + 1; i++) {
		IloNumVarMatrix2x2 ZZ_kr(env, 0);
		for (k = 0; k < kmax; k++) {
			IloNumVarArray ZZ_r(env, 0);
			for (r = 0; r < rmax; r++) {
				sprintf(CharMasterVar, "ZZ_ikr(i%d,k%d,r%d)", i, k, r);
				IloNumVar ZZ(env, 0, IloInfinity, ILOFLOAT, CharMasterVar);
				NoOfMasterVars++;
				ZZ_r.add(ZZ);
			}
			ZZ_kr.add(ZZ_r);
		}
		ZZ_ikr.add(ZZ_kr);
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



	//-------------- Decision Variable Theta_n ---------------------------------------
	/*for (n = 0; n < 1; n++) {
		sprintf(CharMasterVar, "Theta_n(n%d)", n);
		IloNumVar Theta(env, 0, Big_M, ILOFLOAT, CharMasterVar);
		NoOfMasterVars++;
		Theta_n.add(Theta);
	}*/


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

	//-------------------------- Constraint Con9_ZZZX_ijkrm -------------------------
	for (i = 0; i < imax; i++) {
		IloRangeMatrix4x4 Con9_ZZZX_jkrm(env, 0);
		for (j = 1; j < jmax + 1; j++) {
			IloRangeMatrix3x3 Con9_ZZZX_krm(env, 0);
			for (k = 0; k < kmax; k++) {
				IloRangeMatrix2x2 Con9_ZZZX_rm(env, 0);
				for (r = 0; r < rmax; r++) {
					IloRangeArray Con9_ZZZX_m(env, 0);
					for (m = 0; m < mmax; m++) {
						IloExpr expr(env, 0);
						expr += (1 + theta_ijm[i][j][m]) * ZZ_ikr[i][k][r] + zeta_ijm[i][j][m] + s_i[j] - ZZ_ikr[j][k][r] - (1 - X_ijkrm[i][j][k][r][m]) * Big_M;// (DayDuration + theta_ijm[i][j][m] * DayDuration + zeta_ijm[i][j][m] + s_i[j]);
						sprintf(CharMasterCon, "Con9_ZZZX_ijkrm(i%d,j%d,k%d,r%d,m%d)", i, j, k, r, m);
						LBMasterCon = -IloInfinity, UBMasterCon = 0;
						IloRange Con9_ZZZX(env, LBMasterCon, expr, UBMasterCon, CharMasterCon);
						NoOfMasterCons++;
						modelMaster.add(Con9_ZZZX);
						Con9_ZZZX_m.add(Con9_ZZZX);
						expr.end();
					}
					Con9_ZZZX_rm.add(Con9_ZZZX_m);
				}
				Con9_ZZZX_krm.add(Con9_ZZZX_rm);
			}
			Con9_ZZZX_jkrm.add(Con9_ZZZX_krm);
		}
		Con9_ZZZX_ijkrm.add(Con9_ZZZX_jkrm);
	}

	//-------------------------- Constraint Con10a_ZZY_ikr -------------------------
	for (i = 0; i < imax + 1; i++) {
		IloRangeMatrix2x2 Con10a_ZZY_kr(env, 0);
		for (k = 0; k < kmax; k++) {
			IloRangeArray Con10a_ZZY_r(env, 0);
			for (r = 0; r < rmax; r++) {
				IloExpr expr(env, 0);
				expr += ZZ_ikr[i][k][r] - (e_i[i] + s_i[i]) * Y_ikr[i][k][r];
				sprintf(CharMasterCon, "Con10a_ZZY_ikr(i%d,k%d,r%d)", i, k, r);
				LBMasterCon = 0, UBMasterCon = IloInfinity;
				IloRange Con10a_ZZY(env, LBMasterCon, expr, UBMasterCon, CharMasterCon);
				NoOfMasterCons++;
				modelMaster.add(Con10a_ZZY);
				Con10a_ZZY_r.add(Con10a_ZZY);
				expr.end();
			}
			Con10a_ZZY_kr.add(Con10a_ZZY_r);
		}
		Con10a_ZZY_ikr.add(Con10a_ZZY_kr);
	}

	//-------------------------- Constraint Con10b_ZZY_ikr -------------------------
	for (i = 0; i < imax + 1; i++) {
		IloRangeMatrix2x2 Con10b_ZZY_kr(env, 0);
		for (k = 0; k < kmax; k++) {
			IloRangeArray Con10b_ZZY_r(env, 0);
			for (r = 0; r < rmax; r++) {
				IloExpr expr(env, 0);
				expr += ZZ_ikr[i][k][r] - (l_i[i] + s_i[i]) * Y_ikr[i][k][r];
				sprintf(CharMasterCon, "Con10b_ZZY_ikr(i%d,k%d,r%d)", i, k, r);
				LBMasterCon = -IloInfinity, UBMasterCon = 0;
				IloRange Con10b_ZZY(env, LBMasterCon, expr, UBMasterCon, CharMasterCon);
				NoOfMasterCons++;
				modelMaster.add(Con10b_ZZY);
				Con10b_ZZY_r.add(Con10b_ZZY);
				expr.end();
			}
			Con10b_ZZY_kr.add(Con10b_ZZY_r);
		}
		Con10b_ZZY_ikr.add(Con10b_ZZY_kr);
	}

	//-------------------------- Constraint Con11a_ZX_ijkrm -------------------------
	for (i = 0; i < imax + 1; i++) {
		IloRangeMatrix4x4 Con11a_ZX_jkrm(env, 0);
		for (j = 0; j < jmax + 1; j++) {
			IloRangeMatrix3x3 Con11a_ZX_krm(env, 0);
			for (k = 0; k < kmax; k++) {
				IloRangeMatrix2x2 Con11a_ZX_rm(env, 0);
				for (r = 0; r < rmax; r++) {
					IloRangeArray Con11a_ZX_m(env, 0);
					for (m = 1; m < mmax; m++) {
						IloExpr expr(env, 0);
						expr += ZZ_ikr[i][k][r] - w_ijm[i][j][m - 1] * X_ijkrm[i][j][k][r][m] + (1 - X_ijkrm[i][j][k][r][m]) * Big_M;//DayDuration
						sprintf(CharMasterCon, "Con11a_ZX_ijkrm(i%d,j%d,k%d,r%d,m%d)", i, j, k, r, m);
						LBMasterCon = 0, UBMasterCon = IloInfinity;
						IloRange Con11a_ZX(env, LBMasterCon, expr, UBMasterCon, CharMasterCon);
						NoOfMasterCons++;
						modelMaster.add(Con11a_ZX);
						Con11a_ZX_m.add(Con11a_ZX);
						expr.end();
					}
					Con11a_ZX_rm.add(Con11a_ZX_m);
				}
				Con11a_ZX_krm.add(Con11a_ZX_rm);
			}
			Con11a_ZX_jkrm.add(Con11a_ZX_krm);
		}
		Con11a_ZX_ijkrm.add(Con11a_ZX_jkrm);
	}

	//-------------------------- Constraint Con11b_ZX_ijkrm -------------------------
	for (i = 0; i < imax + 1; i++) {
		IloRangeMatrix4x4 Con11b_ZX_jkrm(env, 0);
		for (j = 0; j < jmax + 1; j++) {
			IloRangeMatrix3x3 Con11b_ZX_krm(env, 0);
			for (k = 0; k < kmax; k++) {
				IloRangeMatrix2x2 Con11b_ZX_rm(env, 0);
				for (r = 0; r < rmax; r++) {
					IloRangeArray Con11b_ZX_m(env, 0);
					for (m = 0; m < mmax; m++) {
						IloExpr expr(env, 0);
						expr += ZZ_ikr[i][k][r] - w_ijm[i][j][m] * X_ijkrm[i][j][k][r][m] - (1 - X_ijkrm[i][j][k][r][m]) * Big_M;//DayDuration
						sprintf(CharMasterCon, "Con11b_ZX_ijkrm(i%d,j%d,k%d,r%d,m%d)", i, j, k, r, m);
						LBMasterCon = -IloInfinity, UBMasterCon = 0;
						IloRange Con11b_ZX(env, LBMasterCon, expr, UBMasterCon, CharMasterCon);
						NoOfMasterCons++;
						modelMaster.add(Con11b_ZX);
						Con11b_ZX_m.add(Con11b_ZX);
						expr.end();
					}
					Con11b_ZX_rm.add(Con11b_ZX_m);
				}
				Con11b_ZX_krm.add(Con11b_ZX_rm);
			}
			Con11b_ZX_jkrm.add(Con11b_ZX_krm);
		}
		Con11b_ZX_ijkrm.add(Con11b_ZX_jkrm);
	}

	//-------------------------- Constraint Con12_ZZY_k -------------------------
	for (k = 0; k < kmax; k++) {
		IloExpr expr(env, 0);
		expr += ZZ_ikr[0][k][0];
		for (i = 1; i < imax; i++) {
			expr -= lamda * s_i[i] * Y_ikr[i][k][0];
		}
		sprintf(CharMasterCon, "Con12_ZZY_k(k%d)", k);
		LBMasterCon = 0, UBMasterCon = IloInfinity;
		IloRange Con12_ZZY(env, LBMasterCon, expr, UBMasterCon, CharMasterCon);
		NoOfMasterCons++;
		modelMaster.add(Con12_ZZY);
		Con12_ZZY_k.add(Con12_ZZY);
		expr.end();
	}

	//-------------------------- Constraint Con13_ZZY_kr -------------------------
	for (k = 0; k < kmax; k++) {
		IloRangeArray Con13_ZZY_r(env, 0);
		for (r = 1; r < rmax; r++) {
			IloExpr expr(env, 0);
			expr += ZZ_ikr[0][k][r] - ZZ_ikr[imax][k][r - 1];
			for (i = 1; i < imax; i++) {
				expr -= lamda * s_i[i] * Y_ikr[i][k][r];
			}
			sprintf(CharMasterCon, "Con13_ZZY_kr(k%d,r%d)", k, r);
			LBMasterCon = 0, UBMasterCon = IloInfinity;
			IloRange Con13_ZZY(env, LBMasterCon, expr, UBMasterCon, CharMasterCon);
			NoOfMasterCons++;
			modelMaster.add(Con13_ZZY);
			Con13_ZZY_r.add(Con13_ZZY);
			expr.end();
		}
		Con13_ZZY_kr.add(Con13_ZZY_r);
	}

	//-------------------------- Constraint Con14_ZZY_kr -------------------------
	for (k = 0; k < kmax; k++) {
		IloRangeArray Con14_ZZY_r(env, 0);
		for (r = 0; r < rmax; r++) {
			IloExpr expr(env, 0);
			expr += ZZ_ikr[imax][k][r] - ZZ_ikr[0][k][r];
			for (i = 1; i < imax; i++) {
				expr += lamda * s_i[i] * Y_ikr[i][k][r];
			}
			sprintf(CharMasterCon, "Con14_ZZY_kr(k%d,r%d)", k, r);
			LBMasterCon = -IloInfinity, UBMasterCon = MaxTripDuration;
			IloRange Con14_ZZY(env, LBMasterCon, expr, UBMasterCon, CharMasterCon);
			NoOfMasterCons++;
			modelMaster.add(Con14_ZZY);
			Con14_ZZY_r.add(Con14_ZZY);
			expr.end();
		}
		Con14_ZZY_kr.add(Con14_ZZY_r);
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
	/*
	for (n = 0; n < 1; n++) {
		expr1 += Theta_n[n];
	}*/

	modelMaster.add(IloMinimize(env, expr1));
	expr1.end();

	return 0;
}
int Solve_Master(IloEnv env, IloModel modelMaster_ptr, IloCplex cplexMaster_ptr, bool* InfeasibleMaster, IloNumVarMatrix5x5 X_ijkrm, IloNumVarMatrix3x3 Y_ikr, IloNumVarMatrix3x3 ZZ_ikr) {
	*InfeasibleMaster = false;
	cplexMaster_ptr.extract(modelMaster_ptr);
	//--------------SOLVE MASTER PROBLEM----------------	
	try {
		cplexMaster_ptr.exportModel("CurrentMaster.lp");
		cplexMaster_ptr.setOut(env.getNullStream());
		//cplexMaster_ptr.setParam(IloCplex::EpGap, StopGapMaster);
		cplexMaster_ptr.setParam(IloCplex::TiLim, StopTime);
		cplexMaster_ptr.solve();

		if (!cplexMaster_ptr.solve()) {
			env.error() << "Failed to optimize Master." << endl;
			env.out() << "----------------------------------------------------------------" << endl;
			*InfeasibleMaster = true;
			OptimalOriginalObjFunction = 0;
			Gap = 1;
			SolutionStatus = 0;
			return 0;
		}

		env.out() << "Solution status Master = " << cplexMaster_ptr.getStatus() << endl;
		env.out() << "Solution value Master= " << cplexMaster_ptr.getObjValue() << endl;
		env.out() << "Optimality Gap= " << 100 * cplexMaster_ptr.getMIPRelativeGap() << "%" << endl;
		OptimalOriginalObjFunction = cplexMaster_ptr.getObjValue();
		Gap = cplexMaster_ptr.getMIPRelativeGap();
		SolutionStatus = cplexMaster_ptr.getStatus();

		//--------LOWER BOUND------------
		//LowerBound = cplexMaster_ptr.getObjValue();

		for (k = 0; k < kmax; k++) {
			for (r = 0; r < rmax; r++) {
				for (i = 0; i < imax + 1; i++) {
					for (j = 0; j < jmax + 1; j++) {
						for (m = 0; m < mmax; m++) {
							X_ijkrmValue[i][j][k][r][m] = cplexMaster_ptr.getValue(X_ijkrm[i][j][k][r][m]);
							//if (X_ijValue[i][j] < 0.001) X_ijValue[i][j] = 0;
							//if (X_ijkrmValue[i][j][k][r][m] != 0) cout << "X_ijkrm[" << i << "][" << j << "][" << k << "][" << r << "][" << m << "]=" << X_ijkrmValue[i][j][k][r][m] << endl;
						}
					}
				}
			}
		}

		for (i = 0; i < imax + 1; i++) {
			for (k = 0; k < kmax; k++) {
				for (r = 0; r < rmax; r++) {
					Y_ikrValue[i][k][r] = cplexMaster_ptr.getValue(Y_ikr[i][k][r]);
					//if (Y_jValue[j] < 0.001) Y_jValue[j] = 0;
					//if (Y_ikrValue[i][k][r] != 0) cout << "Y_ikr[" << i << "][" << k << "][" << r << "]=" << Y_ikrValue[i][k][r] << endl;
				}
			}
		}
		for (k = 0; k < kmax; k++) {
			for (r = 0; r < rmax; r++) {
				for (i = 0; i < imax + 1; i++) {
					ZZ_ikrValue[i][k][r] = cplexMaster_ptr.getValue(ZZ_ikr[i][k][r]);
					//if (ZZ_ikrValue[i][k][r] != 0) cout << "ZZ_ikr[" << i << "][" << k << "][" << r << "]=" << ZZ_ikrValue[i][k][r] << endl;
				}
			}
		}

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



		/*std::ostringstream osSolution;
		osSolution << "C:\\Data_TSPLIB\\RESULTS\\Nodes=" << cus << "\\Combination=" << CombinationOfSlaveProblems_String << "\\SolutionBENDERS.txt";
		std::string FileNameSolution = osSolution.str();
		std::ofstream fsSolution;
		fsSolution.open(FileNameSolution.c_str(), std::ios::out);*/
		//ofstream solution;
		//solution.open("C:/Data_Athinaki/BENDERS/Nodes=" << cus << "/Combination=" << CombinationOfSlaveProblems<<"/SolutionBENDERS.txt");
		//solution.open("C:/Users/zoigr/Dropbox/GYR UTH_EA/Actions/Action B2/Zoi - Action B2/TSP/Solution.txt");
		cout << "Vehicle" << "	" << "Route" << "	" << "BreakPoint" << "	" << "From " << "	" << "To " << "	" << "DepartureTime" << endl;
		int test = 0;
		double distance = 0;
		for (k = 0; k < kmax; k++) {
			for (r = 0; r < rmax; r++) {
				for (m = 0; m < mmax; m++) {
					for (i = 0; i < 1; i++) {
						for (j = 1; j < jmax + 1; j++) {
							if (X_ijkrmValue[i][j][k][r][m] > 0.9) {
								test = j;
								//distance = distance + Distance_ij[i][j];
								cout << k << "	" << r << "	" << m << "	" << i << "	" << j << "	" << ZZ_ikrValue[i][k][r] << endl;//<< Z_ijkrmValue[i][j][k][r][m] << "	"
								goto Restart;
							}
						}
					}
				}
			Restart:;
				for (m = 0; m < mmax; m++) {
					for (i = 0; i < imax; i++) {
						if (test != 0) {
							if (i == test) {
								for (j = 0; j < jmax + 1; j++) {
									if (X_ijkrmValue[i][j][k][r][m] > 0.9) {
										test = j;
										//distance = distance + Distance_ij[i][j];
										cout << k << "	" << r << "	" << m << "	" << i << "	" << j << "	" << ZZ_ikrValue[i][k][r] << endl;//<< Z_ijkrmValue[i][j][k][r][m] << "	"
										if (test == jmax) {
											cout << k << "	" << r << "	" << m << "	" << i << "	" << j << "	" << ZZ_ikrValue[imax][k][r] << endl;
										}
										i = 0;
										goto Restart;
									}
								}
							}
						}
						else break;
					}

				}
				cout << "-----------------------------------------------------	" << endl;
			}
		}

		/*fsSolution.close();*/



	//for (n = 0; n < 1; n++) {
	//	ThetaValue = cplexMaster_ptr.getValue(Theta_n[n]);
	//	//if (ThetaValue != 0) cout << "ThetaValue=" << ThetaValue << endl;
	//}
	//*DTransposeY_ptr = LowerBound - ThetaValue;
	//dTy.push_back(*DTransposeY_ptr);
	//zCurrent.push_back(ThetaValue);

	//OptimalThetaValue = ThetaValue;

	}
	catch (IloException& e) {
		cerr << "concert exception caught Master:" << e << endl;
	}
	catch (...) {
		cerr << "Unknown exception caught Master " << endl;
	}
	return 0;
}
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
	//cout << FileName_Problem_ptr << endl;
	sprintf(filepath, "%s/%s", FilePath_Results_ptr, FileName_Problem_ptr);
	//string stringpath = filepath;
	status = mkdir(filepath);
	sprintf(filepath, "%s/%s/%s_DATA_CustomersData.txt", FilePath_Results_ptr, FileName_Problem_ptr, FileName_Problem_ptr);
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

	sprintf(filepath, "%s/%s/%s_DATA_DistanceMatrix.txt", FilePath_Results_ptr, FileName_Problem_ptr, FileName_Problem_ptr);
	outfile.open(filepath);
	for (int i = 0; i < imax + 1; i++) {
		for (int j = 0; j < jmax + 1; j++) {
			outfile << Distance_ij[i][j] << '\t';
		}
		outfile << std::endl;
	}
	outfile.close();

	sprintf(filepath, "%s/%s/%s_DATA_EdgeCategory.txt", FilePath_Results_ptr, FileName_Problem_ptr, FileName_Problem_ptr);
	outfile.open(filepath);
	for (int i = 0; i < imax + 1; i++) {
		for (int j = 0; j < jmax + 1; j++) {
			outfile << EdgeCat_ij[i][j] << '\t';
		}
		outfile << std::endl;
	}
	outfile.close();

	sprintf(filepath, "%s/%s/%s_DATA_SpeedCategoryOverTime.txt", FilePath_Results_ptr, FileName_Problem_ptr, FileName_Problem_ptr);
	outfile.open(filepath);
	for (int p = 0; p < pmax; p++) {
		for (int c = 0; c < cmax; c++) {
			outfile << SpeedOfCatOverTime_p_c[p][c] << '\t';
		}
		outfile << std::endl;
	}
	outfile.close();

	sprintf(filepath, "%s/%s/%s_DATA_TravelTimeBreakpoints.txt", FilePath_Results_ptr, FileName_Problem_ptr, FileName_Problem_ptr);
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

	sprintf(filepath, "%s/%s/%s_DATA_TravelTime.txt", FilePath_Results_ptr, FileName_Problem_ptr, FileName_Problem_ptr);
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

	sprintf(filepath, "%s/%s/%s_DATA_TravelTimeCalculated.txt", FilePath_Results_ptr, FileName_Problem_ptr, FileName_Problem_ptr);
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

	sprintf(filepath, "%s/%s/%s_DATA_Theta.txt", FilePath_Results_ptr, FileName_Problem_ptr, FileName_Problem_ptr);
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

	sprintf(filepath, "%s/%s/%s_DATA_Zeta.txt", FilePath_Results_ptr, FileName_Problem_ptr, FileName_Problem_ptr);
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
int PrintOptimalSolution(char* FilePath_Results_ptr) {
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
	sprintf(filepath, "%s/%s/%s_CPLEX_OptimalSolution.txt", FilePath_Results_ptr, FileName_Problem_ptr, FileName_Problem_ptr);
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
	if (SolutionStatus == 1) {
		outfile << "Solution Status= " << "Feasible" << std::endl;
	}
	else if (SolutionStatus == 2) {
		outfile << "Solution Status= " << "Optimal" << std::endl;
	}
	else if (SolutionStatus == 0) {
		outfile << "Solution Status= " << "Infeasible" << std::endl;
	}
	else {
		outfile << "Solution Status= " << SolutionStatus << std::endl;
	}
	outfile << "Model Constraints= " << NoOfMasterCons << std::endl;
	outfile << "Model Variables= " << NoOfMasterVars << std::endl;

	/*outfile << "OptimalMasterObjFunction= " << OptimalMasterObjFunction << std::endl;
	outfile << "OptimalSlaveObjFunction= " << OptimalSlaveObjFunction << std::endl;*/
	outfile << "----------------------------------" << std::endl;
	/*if (OptimalThetaValue > 0.01) {
		outfile << "OptimalThetaValue= " << OptimalThetaValue << std::endl;
	}*/
	/*outfile << "----------------------------------" << std::endl;
	outfile << "TotalNumberOfFeasibilityCuts= " << BDFeasCuts << std::endl;
	outfile << "TotalNumberOfOptimalityCuts= " << BDOptCuts << std::endl;
	outfile << "TotalNumberOfMasterVariables= " << NoOfMasterVars << std::endl;
	outfile << "TotalNumberOfSlaveVariables= " << NoOfSlaveVars << std::endl;
	outfile << "TotalNumberOfMasterConstraints= " << NoOfMasterCons << std::endl;
	outfile << "TotalNumberOfSlaveConstraints= " << NoOfSlaveCons << std::endl;*/
	if (SolutionStatus != 0) {
		for (k = 0; k < kmax; k++) {
			for (r = 0; r < rmax; r++) {
				outfile << "Veh - Trip:" << k << "	" << r << endl;
				for (m = 0; m < mmax; m++) {
					for (i = 0; i < 1; i++) {
						for (j = 1; j < jmax + 1; j++) {
							if (X_ijkrmValue[i][j][k][r][m] > 0.9) {
								test = j;
								//distance = distance + Distance_ij[i][j];
								outfile << i << "	" << ZZ_ikrValue[i][k][r] << endl;
								outfile << j << "	" << ZZ_ikrValue[j][k][r] << endl;
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
									if (X_ijkrmValue[i][j][k][r][m] > 0.9) {
										test = j;
										//distance = distance + Distance_ij[i][j];
										outfile << j << "	" << ZZ_ikrValue[j][k][r] << endl;
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

	sprintf(filepath, "%s/%s/%s_CPLEX_Variables.txt", FilePath_Results_ptr, FileName_Problem_ptr, FileName_Problem_ptr);
	outfile.open(filepath);
	if (SolutionStatus != 0) {
		for (k = 0; k < kmax; k++) {
			for (r = 0; r < rmax; r++) {
				for (i = 0; i < imax + 1; i++) {
					for (j = 0; j < jmax + 1; j++) {
						for (m = 0; m < mmax; m++) {
							if (X_ijkrmValue[i][j][k][r][m] >= 0.01) outfile << "X_ijkrm[" << i << "][" << j << "][" << k << "][" << r << "][" << m << "]=" << X_ijkrmValue[i][j][k][r][m] << endl;
						}
					}
				}
			}
		}
		outfile << "----------------------------------" << std::endl;
		for (i = 0; i < imax + 1; i++) {
			for (k = 0; k < kmax; k++) {
				for (r = 0; r < rmax; r++) {
					if (Y_ikrValue[i][k][r] >= 0.01) outfile << "Y_ikr[" << i << "][" << k << "][" << r << "]=" << Y_ikrValue[i][k][r] << endl;
				}
			}
		}
		outfile << "----------------------------------" << std::endl;
		for (k = 0; k < kmax; k++) {
			for (r = 0; r < rmax; r++) {
				for (i = 0; i < imax + 1; i++) {
					if (ZZ_ikrValue[i][k][r] >= 0.01) outfile << "ZZ_ikr[" << i << "][" << k << "][" << r << "]=" << ZZ_ikrValue[i][k][r] << endl;
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

	for (int i_Problem = 0; i_Problem < TotalNoOfProblems; i_Problem++) {
		if (i_Problem < 8 || i_Problem>18) {
			strcpy(FileName_Problem, ProblemNames[i_Problem].c_str());
			cout << "-------------------" << endl;
			cout << "Solving DataSet: " << FileName_Problem << endl;
			//--------Declare the environment of CPLEX----------------
			IloEnv env;
			try {
				//--------Construct models----------------
				IloModel modelSlave(env);
				IloModel modelMaster(env);

				//------Declare Master Decision Variables----------
				IloNumVarMatrix5x5 X_ijkrm(env, 0);//equal to 1 if and only if vehicle k leaves node i toward node j during time interval m in the r - th trip
				IloNumVarMatrix3x3 Y_ikr(env, 0);//equal to 1 if and only if a vehicle visits node i in the r-th trip
				//IloNumVarMatrix5x5 Z_ijkrm(env, 0); //departure time of the r-th trip by vehicle k from node i toward node j in time interval m
				IloNumVarMatrix3x3 ZZ_ikr(env, 0);//departure time of the r-th trip by vehicle k from node i ∈ V+ or arrival time of the r - th trip by vehicle k at node n + 1
				//IloNumVarArray Theta_n(env, 0);//continuous variable that takes the value of the expansion needed to be made at WWTP at location j in terms of additional amount of waste water that can be treated in it.

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
				IloRangeMatrix5x5 Con9_ZZZX_ijkrm(env, 0);
				IloRangeMatrix3x3 Con10a_ZZY_ikr(env, 0);
				IloRangeMatrix3x3 Con10b_ZZY_ikr(env, 0);
				IloRangeMatrix5x5 Con11a_ZX_ijkrm(env, 0);
				IloRangeMatrix5x5 Con11b_ZX_ijkrm(env, 0);
				IloRangeArray Con12_ZZY_k(env, 0);
				IloRangeMatrix2x2 Con13_ZZY_kr(env, 0);
				IloRangeMatrix2x2 Con14_ZZY_kr(env, 0);
				IloRangeArray ConAuxiliary_i(env, 0);

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
				start = clock();
				auto TimeNow = std::chrono::system_clock::now();
				std::time_t CurTime = std::chrono::system_clock::to_time_t(TimeNow);
				std::cout << "Started at " << std::ctime(&CurTime);
				cout << "Building Model..." << endl;
				status = do_master(env, modelMaster, X_ijkrm, Y_ikr, ZZ_ikr, Con2_YX_kr, Con3_YX_kr, Con4a_YX_ikr, Con4b_YX_ikr, Con5_Y_i, Con6_Y_kr, Con7_ZZZ_ikr, Con8_ZZZ_kr, Con9_ZZZX_ijkrm, Con10a_ZZY_ikr, Con10b_ZZY_ikr, Con11a_ZX_ijkrm, Con11b_ZX_ijkrm, Con12_ZZY_k, Con13_ZZY_kr, Con14_ZZY_kr, ConAuxiliary_i);
				if (status != 0) {
					Found_Error("do_master");
					return -1;
				}

				/*status = do_slave();
				if (status != 0) {
					Found_Error("do_slave");
					return -1;
				}

				status = BendersIteration(modelMaster, modelSlave);
				if (status != 0) {
					Found_Error("BendersIteration");
					return -1;
				}*/

				IloCplex cplexMaster(env);
				/*cplexMaster.extract(modelMaster_ptr);
				cplexMaster.exportModel("modelMaster.lp");*/
				cout << "Solving Model..." << endl;
				status = Solve_Master(env, modelMaster, cplexMaster, &InfeasibleMaster, X_ijkrm, Y_ikr, ZZ_ikr);
				if (status != 0) {
					Found_Error("Solve_Master");
					return -1;
				}
				if (InfeasibleMaster == true) {
					cout << "The Model is infeasible. Check data and formulation." << endl;
				}
				stop = clock();
				duration = (long double)(stop - start) / CLOCKS_PER_SEC;
				cout << "Printing solution..." << endl;
				status = PrintOptimalSolution(FilePath_Results);
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
		}
	}
	return 0;
}//End main
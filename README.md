# Veda - A Proof-Checking System
## Introduction
Veda is a new proof-checking system (a proof checker or a proof assistant) intended for checking mathematical texts (usally containing definitions and proofs)
written in the formal mathematical language V (see V.pdf in the current repo). 

It can be useful, for instance, to students studying (or self-studying) a mathematical discipline. 
Currently, these disciplines are elementary mathematical logic, elementary set theory and elements of group theory.
The student can write her own proofs and the system will check them for correctness. See the text file learn.v with proof examples in elementary mathematical logic
and set theory.
# Veda_22 and Veda_6. 
There are currently 2 versions of the system: Veda_22 and Veda_6. Both are Visual C++ console applications.
Veda_22 was compiled and built in Visual Studo 2022 under Windows 10. It can be installed using the installer veda22Setup.exe. The installer is in the repo.

Veda_6 was compiled and built in Visual Studo 6.0 (VS6.0). The C++ compiler VC++ 6.0 was installed  in Windows XP, Windows 7 and Windows 10.
Veda_6 can work only if the Visual Studio 6.0 with C++ is installed. It can be downloaded, for instance, from
https://www.mediafire.com/file/67jbynw9h7bt6d1/VS98.rar/file
The reason for using Veda_6 is that it for big modules is much faster than Veda_22. But for the student use it is ineesential.
## Veda projects
To use Veda system you should create a Veda project. A Veda project is a folder containing the following files:

1. One or more v-files. These are text files with the .v extension. A v-file contains a V-module, which has the following form:
module M;
use M1, ..., Mk;
[
<Definitions and Proofs>
]
Here M,M1, ..., Mk are module names. We say that the module M depends on the modules M1, ..., Mk. 
The modules  M1, ..., Mk must be checked before checking M. 

2. The file all.txt. Contains the list all modules in the project.

3. The file tabs.txt. Contains the list of all names used in the modules M,M1, ..., Mk. Can contain some other names.

4. The file fubs.chr. Contains all operators of the V language. See V_syntax.txt.

5. The file d.d. It is the "control panel" of the system. Contains, in particular, the name N of a module in the project, which has to be checked.
The system after checking the module N will automatically check all modules which are depend(directly or indirectly) on the module N.
The file d.d is described in detail inside the module d.d.

Currently, there are 3 projects:

1. C:\Veda\Veda_22_learn. Contains 2 v-files: 
a) 0_root.v - elementary mathematical logic and set theory;
b) 1_learn.v - a tutorial file( and a "sandbox") for elementary mathematical logic and set theory;

2. C:\veda\Veda_22. Contains 3 v-files:
a) 0_root.v - see above;
b) 1_group.v - elements of group theory.
c) 2_altg.v - elements of permutation theory necessary for definition of the alternating group.

3. C:\Veda\Veda_6.
This project can   
##Intallation
To install Veda_22:
1. Download the file veda22Setup.exe (see this repo).
2. Run it. The system should be installed in the directory c:\ProgramFiles\ as Veda22.
3. Dowoload the file Veda.rar to the download folder and unzip it there. The unzipped folder named Veda should contain the following 4 folsders:
Veda_6, Veda_22_learn, Files_for_Veda_22, Veda_22, and 1 file Project.txt, the first line in it is:
c:\Veda\Veda_22_learn
This is the full path of the Veda project Veda_22_learn.
A Veda project is a folder containing 

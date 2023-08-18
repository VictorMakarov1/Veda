# Veda - A Proof-Checking System
## Introduction
Veda is a new proof-checking system (a proof checker or a proof assistant) intended for checking mathematical texts (usually containing definitions and proofs)
written in the formal mathematical language V (see V6_short.pdf in this repo). 

It can be useful, for instance, to students studying (or self-studying) a mathematical discipline. 
Currently, these disciplines are elementary mathematical logic, elementary set theory. and elements of group theory.
The student can write her own proofs and the system will check them for correctness. See the text file learn.v with proof examples in elementary mathematical logic
and set theory.
## Veda22 and Veda6 
There are currently 2 versions of the system: Veda22 and Veda6. Both are Visual C++ console applications.

Veda22 was compiled and built in Visual Studo 2022 under Windows 10.
For installing Veda22 see the text file Install_Veda22.txt or the section "How to install Veda22" below.

Veda6 was compiled and built in Visual Studo 6.0 (VS6.0).
Visual Studio 6.0 is available at https://www.mediafire.com/file/67jbynw9h7bt6d1/VS98.rar/file
For installing Veda6 see the text file Install_Veda6.txt 

The reason for using Veda6 is that for big modules it works much faster than Veda22. But for the student writing small proofs it is inessential.

For using Veda22 or Veda6 see the text file Using_Veda.txt.

## Files in this repo

1. 0_root.v - elementary mathematical logic and set theory;
2. 1_group.v - the basics of group theory, including the isomorphism theorems;
3. 2_altg.v - the basics of the permutation theory, necessary for defining the alternating group;
4. 1_learn.v - propositional logic;
5. Install_Veda22.txt - detailed instructions on how to install Veda22;
6. Newveda_C4.zip - the source code (cpp- and h-files) for Veda6;
7. V6_short.pdf - a short description of the V language; 
8. Veda.rar - see Install_Veda22.txt;
9. Veda22Setup.exe - the setup program for installing Veda22;
10. Veda22_cpp_h.rar - the source code (cpp- and h-files) for Veda22.

## How to install Veda22

Veda22.exe runs on x64 computers and requires Windows 10  (not tested yet on Windows 11).

1. Download from this repo Veda22Setup.exe and Veda.rar to the download folder.

2. Run Veda22Setup.exe as administrator.

3. Veda22Setup.exe will create a new folder in C:\Program Files named Veda22 
   and put to it Veda22.exe(the system Veda22).

4. Create a shortcut on the descktop for Veda22.exe.

5. Unrar Veda.rar.

6. You will see the folder Veda containing the file Project.txt and 2 folders:
   LearnV and GroupTheory.

7. Copy the folder Veda to your C drive.

8. Double-click the shortcut for Veda22.exe which you have created before.

9. Veda22 will check the file learn.v.

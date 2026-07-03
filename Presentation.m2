--We worked on both gfanInterface.m2 and Tropical.m2


--Most tropical geometry functionality in M2 calls the program
-- gfan by Anders Jensen to do the actual computations.

--The package gfanInterface.m2 interfaces between gfan and M2.
--This was written years ago, and and had not been maintained recently.
--We fixed some bugs, and wrote wrappers for some commands that had been
--introduced to gfan more recently.

--***Show documentation for gfanTropicalPrevariety

--We also fixed tests, so the test score went from 41 to >50




--At a previous workshop we started to implement functionality for nonconstant coefficient
--tropical varieties.

--We fixed some bugs with this and improved some algorithms.

R = QQ[x,y,z]

I=ideal(2*x+3*y+5*z);

T1 = gfanVarietyWithpadicVal(I,p=>2)

F1= fan(T1);
vertices F1;

T2 = gfanVarietyWithpadicVal(I,p=>3)
F2= fan(T2);
vertices F2;

T3 = gfanVarietyWithpadicVal(I,p=>5)
F3= fan(T3);
vertices F3;



--Still to do


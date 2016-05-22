(*^

::[	frontEndVersion = "Microsoft Windows Mathematica Notebook Front End Version 2.2";
	microsoftWindowsStandardFontEncoding;
	fontset = title, "Arial", 24, L0, center, nohscroll, bold;
	fontset = subtitle, "Arial", 18, L0, center, nohscroll, bold;
	fontset = subsubtitle, "Arial", 14, L0, center, nohscroll, bold;
	fontset = section, "Arial", 14, L0, bold, grayBox;
	fontset = subsection, "Arial", 12, L0, bold, blackBox;
	fontset = subsubsection, "Arial", 10, L0, bold, whiteBox;
	fontset = text, "Arial", 12, L0;
	fontset = smalltext, "Arial", 10, L0;
	fontset = input, "Courier New", 12, L0, nowordwrap, bold;
	fontset = output, "Courier New", 12, L0, nowordwrap;
	fontset = message, "Courier New", 10, L0, nowordwrap, R65280;
	fontset = print, "Courier New", 10, L0, nowordwrap;
	fontset = info, "Courier New", 10, L0, nowordwrap;
	fontset = postscript, "Courier New", 8, L0, nowordwrap;
	fontset = name, "Arial", 10, L0, nohscroll, italic, B65280;
	fontset = header, "Times New Roman", 10, L0, right, nohscroll;
	fontset = footer, "Times New Roman", 10, L0, right, nohscroll;
	fontset = help, "Arial", 10, L0, nohscroll;
	fontset = clipboard, "Arial", 12, L0, nohscroll;
	fontset = completions, "Arial", 12, L0, nowordwrap, nohscroll;
	fontset = graphics, "Courier New", 10, L0, nowordwrap, nohscroll;
	fontset = special1, "Arial", 12, L0, nowordwrap, nohscroll;
	fontset = special2, "Arial", 12, L0, center, nowordwrap, nohscroll;
	fontset = special3, "Arial", 12, L0, right, nowordwrap, nohscroll;
	fontset = special4, "Arial", 12, L0, nowordwrap, nohscroll;
	fontset = special5, "Arial", 12, L0, nowordwrap, nohscroll;
	fontset = leftheader, "Arial", 12, L0, nowordwrap, nohscroll;
	fontset = leftfooter, "Arial", 12, L0, nowordwrap, nohscroll;
	fontset = reserved1, "Courier New", 10, L0, nowordwrap, nohscroll;]
:[font = title; inactive; nohscroll; center; ]
Using GITT package - Samples
:[font = text; inactive; ]
This notebook demonstrates the use of the second version of the GITT package which implements some  formalisms of the Generalized Integral Transform Technique. The "gitt.m" and "citt.m" files should be placed in PACKAGES\CALCULUS subdirectory under WNMATH22 path.
:[font = section; inactive; startGroup; ]
Load GITT package
:[font = input; startGroup; Cclosed; nowordwrap; ]
<<Calculus`GITT`
GITT::usage
:[font = output; inactive; formatted; output; endGroup; endGroup; nowordwrap; ]
"GITT[eqgov,eqicbc,unknown,nterms,t,{{x,xi,xf},...},flt,v,f,unknownt,\
  opt] transforms one partial differential equation (PDE) in a finite\
  ordinary differential equation (ODE) system by applying the\
  Generalized Integral Transform Technique (GITT) and gives a\
  four-element list: [[1]] the inversion formula for the specified\
  unknown. [[2]] the finite transformed ODE system with independent\
  variable t. [[3]] the initial conditions for the finite transformed\
  ODE system. [[4]] the transformed unknowns for the finite\
  transformed ODE system. The argument eqgov is the PDE to be\
  transformed. The argument eqicbc is a list containing initial and\
  boundary conditions. The argument unknown is the unknown variable.\
  The argument nterms is the truncation order number. The argument t\
  is the independent variable for the transformed ODE. The argument x\
  is an independent variable to be transformed. The arguments xi,xf\
  are the limits of domain of x. The argument flt is a filter\
  function that satisfies boundary conditions. The argument v is any\
  symbol to identify the eigenvalues. The argument f is any symbol to\
  identify the eigenfunctions. The argument unknownt is any symbol to\
  identify the transformed unknown. The argument opt is used to\
  define options like WorkingPrecision->d. The Calculus`CITT` and\
  Algebra`Trigonometry` packages are used."



;[o]
GITT[eqgov,eqicbc,unknown,nterms,t,{{x,xi,xf},...},flt,v,f,unknownt,o\
 
 pt] transforms one partial differential equation (PDE) in a finite\
 
 ordinary differential equation (ODE) system by applying the\
 
 Generalized Integral Transform Technique (GITT) and gives a\
 
 four-element list: [[1]] the inversion formula for the specified\
 
 unknown. [[2]] the finite transformed ODE system with independent\
 
 variable t. [[3]] the initial conditions for the finite transformed\
 
 ODE system. [[4]] the transformed unknowns for the finite\
 
 transformed ODE system. The argument eqgov is the PDE to be\
 
 transformed. The argument eqicbc is a list containing initial and\
 
 boundary conditions. The argument unknown is the unknown variable.\
 
 The argument nterms is the truncation order number. The argument t\
 
 is the independent variable for the transformed ODE. The argument x\
 
 is an independent variable to be transformed. The arguments xi,xf\
 
 are the limits of domain of x. The argument flt is a filter function\
 
 that satisfies boundary conditions. The argument v is any symbol to\
 
 identify the eigenvalues. The argument f is any symbol to identify\
 
 the eigenfunctions. The argument unknownt is any symbol to identify\
 
 the transformed unknown. The argument opt is used to define options\
 
 like WorkingPrecision->d. The Calculus`CITT` and\
 
 Algebra`Trigonometry` packages are used.
:[font = section; inactive; startGroup; backColorRed = 65280; backColorGreen = 65280; backColorBlue = 65280; fontColorRed = 0; fontColorGreen = 0; fontColorBlue = 0; bold; fontName = "Arial"; fontSize = 14; ]
Parabolic Problem (Nb7b)
:[font = subsection; inactive; startGroup; backColorRed = 65280; backColorGreen = 65280; backColorBlue = 65280; fontColorRed = 0; fontColorGreen = 0; fontColorBlue = 0; bold; fontName = "Arial"; fontSize = 12; ]
Definition
:[font = input; startGroup; nowordwrap; backColorRed = 65280; backColorGreen = 65280; backColorBlue = 65280; fontColorRed = 0; fontColorGreen = 0; fontColorBlue = 0; bold; fontName = "Courier New"; fontSize = 12; ]
eqgov=(D[u[x,t],t]==D[u[x,t],x,x])

eqicbc={ u[x,0]==0
	,D[u[x,t],x]==0 /. x->0
	,D[u[x,t],x]==1 /. x->1 }
:[font = output; inactive; formatted; output; nowordwrap; ]
Derivative[0, 1][u][x, t] == Derivative[2, 0][u][x, t]



;[o]
 (0,1)           (2,0)
u     [x, t] == u     [x, t]
:[font = output; inactive; formatted; output; endGroup; endGroup; nowordwrap; ]
{u[x, 0] == 0, Derivative[1, 0][u][0, t] == 0, 
  Derivative[1, 0][u][1, t] == 1}



;[o]
                (1,0)              (1,0)
{u[x, 0] == 0, u     [0, t] == 0, u     [1, t] == 1}
:[font = subsection; inactive; startGroup; backColorRed = 65280; backColorGreen = 65280; backColorBlue = 65280; fontColorRed = 0; fontColorGreen = 0; fontColorBlue = 0; bold; fontName = "Arial"; fontSize = 12; ]
Solution
:[font = input; startGroup; nowordwrap; backColorRed = 65280; backColorGreen = 65280; backColorBlue = 65280; fontColorRed = 0; fontColorGreen = 0; fontColorBlue = 0; bold; fontName = "Courier New"; fontSize = 12; ]
sol=GITT[eqgov,eqicbc,u[x,t],5,t,{{x,0,1}},t+(x^2-1/3)/2,
	mi,qsi,gama,WorkingPrecision->10];
anasol=Simplify[Chop[sol[[1]] /.
	First[DSolve[Join[sol[[2]],sol[[3]]],sol[[4]],t]]]]
Table[Evaluate[u[x,0.1] /. anasol],{x,0,1,0.1}]
:[font = print; inactive; formatted; output; nowordwrap; ]
No Input Form Generated


;[o]
Homogeneous Problem:
     (0,1)             (2,0)
{(uH)     [x, t] - (uH)     [x, t] == 0, 
 
          2
    1    x                       (1,0)
 {-(-) + -- + uH[x, 0] == 0, (uH)     [0, t] == 0, 
    6    2
 
      (1,0)
  (uH)     [1, t] == 0}}

Auxiliary Problem:
                2
{-qsi''[x] == mi  qsi[x], {qsi'[0] == 0, qsi'[1] == 0}}

EigenValues:
{0., 3.14159, 6.28319, 9.42478, 12.5664}

Normalized EigenFunction:
{1, 1.41421 Cos[3.14159 x], 1.41421 Cos[6.28319 x], 
 
 1.41421 Cos[9.42478 x], 1.41421 Cos[12.5664 x]}

Transformed ODE System:
  2
mi  gama[t] + gama'[t] == 0

 -defIntegral[qsi[x], {x, 0, 1}]
{------------------------------- + 
                6
 
                2
   defIntegral[x  qsi[x], {x, 0, 1}]
   --------------------------------- + gama[0] == 0}
                   2

:[font = output; inactive; formatted; output; nowordwrap; ]
u[x_, t_] -> -1/6 + t + x^2/2 + 
   (0.2026423673746096*Cos[3.14159265162641*x])/
    E^(9.86960438875306*t) - 
   (0.05066059187499902*Cos[6.283185307908482*x])/
    E^(39.47841761351699*t) + 
   (0.02251581848910294*Cos[9.42477795916618*x])/
    E^(88.8264395795846*t) - 
   (0.01266514806783543*Cos[12.56637061665502*x])/
    E^(157.9136704751308*t)



;[o]
                         2
               1        x    0.202642 Cos[3.14159 x]
u[x_, t_] -> -(-) + t + -- + ----------------------- - 
               6        2            9.8696 t
                                    E
 
  0.0506606 Cos[6.28319 x]   0.0225158 Cos[9.42478 x]
  ------------------------ + ------------------------ - 
          39.4784 t                  88.8264 t
         E                          E
 
  0.0126651 Cos[12.5664 x]
  ------------------------
          157.914 t
         E
:[font = output; inactive; formatted; output; endGroup; endGroup; endGroup; nowordwrap; ]
{0.007885293021678314, 0.00937417888279999, 0.01413242611678607, 
  0.02302574979068376, 0.03746061009019244, 0.05931089377712247, 
  0.0907877843774905, 0.1342450864565521, 0.1919300768580705, 
  0.2657107579988393, 0.3568262458819805}



;[o]
{0.00788529, 0.00937418, 0.0141324, 0.0230257, 0.0374606, 0.0593109, 
 
 0.0907878, 0.134245, 0.19193, 0.265711, 0.356826}
:[font = section; inactive; startGroup; ]
Parabolic Problem (Nb7c)
:[font = subsection; inactive; startGroup; ]
Definition
:[font = input; startGroup; nowordwrap; ]
bi=2;
eqgov=(D[u[x,t],t]==D[u[x,t],x,x])

eqicbc={ u[x,0]==1
	,D[u[x,t],x]==0 /. x->0
	,D[u[x,t],x] + bi u[x,t]==0 /. x->1 }
:[font = output; inactive; formatted; output; nowordwrap; ]
Derivative[0, 1][u][x, t] == Derivative[2, 0][u][x, t]



;[o]
 (0,1)           (2,0)
u     [x, t] == u     [x, t]
:[font = output; inactive; formatted; output; endGroup; endGroup; nowordwrap; ]
{u[x, 0] == 1, Derivative[1, 0][u][0, t] == 0, 
  2*u[1, t] + Derivative[1, 0][u][1, t] == 0}



;[o]
                (1,0)                          (1,0)
{u[x, 0] == 1, u     [0, t] == 0, 2 u[1, t] + u     [1, t] == 0}
:[font = subsection; inactive; startGroup; ]
Solution
:[font = input; startGroup; nowordwrap; ]
sol=GITT[eqgov,eqicbc,u[x,t],5,t,{{x,0,1}},0,
	mi,qsi,gama,WorkingPrecision->10];
anasol=Simplify[Chop[sol[[1]] /.
	First[DSolve[Join[sol[[2]],sol[[3]]],sol[[4]],t]]]]
Table[Evaluate[u[x,0.1] /. anasol],{x,0,1,0.1}]
:[font = print; inactive; formatted; output; nowordwrap; ]
No Input Form Generated


;[o]
Auxiliary Problem:
                2
{-qsi''[x] == mi  qsi[x], {qsi'[0] == 0, 2 qsi[1] + qsi'[1] == 0}}

EigenValues:
{1.07687, 3.6436, 6.57833, 9.62956, 12.7223}

Normalized EigenFunction:
{1.20055 Cos[1.07687 x], 1.33884 Cos[3.6436 x], 
 
 1.38522 Cos[6.57833 x], 1.39982 Cos[9.62956 x], 
 
 1.40576 Cos[12.7223 x]}

Transformed ODE System:
  2
mi  gama[t] + gama'[t] == 0

{gama[0] == defIntegral[qsi[x], {x, 0, 1}]}

:[font = output; inactive; formatted; output; nowordwrap; ]
u[x_, t_] -> (1.17845578787451*Cos[1.076873988204255*x])/
    E^(1.159657586470937*t) - 
   (0.2367209862614179*Cos[3.643597896163739*x])/
    E^(13.27580562892882*t) + 
   (0.0848467938556275*Cos[6.578333728401178*x])/
    E^(43.27447464222053*t) - 
   (0.04137979813641896*Cos[9.62956034429177*x])/
    E^(92.7284324243567*t) + 
   (0.02412248200991162*Cos[12.72229877129918*x])/
    E^(161.8568860262005*t)



;[o]
             1.17846 Cos[1.07687 x]   0.236721 Cos[3.6436 x]
u[x_, t_] -> ---------------------- - ---------------------- + 
                    1.15966 t                13.2758 t
                   E                        E
 
  0.0848468 Cos[6.57833 x]   0.0413798 Cos[9.62956 x]
  ------------------------ - ------------------------ + 
          43.2745 t                  92.7284 t
         E                          E
 
  0.0241225 Cos[12.7223 x]
  ------------------------
          161.857 t
         E
:[font = output; inactive; formatted; output; endGroup; endGroup; endGroup; nowordwrap; ]
{0.987778832436081, 0.985587783315256, 0.978640251117676, 
  0.965843796558479, 0.945486701190044, 0.915419720002882, 
  0.873331135164165, 0.817105589729788, 0.7452270299522886, 
  0.6571569102595643, 0.5536042100422255}



;[o]
{0.987779, 0.985588, 0.97864, 0.965844, 0.945487, 0.91542, 0.873331, 
 
 0.817106, 0.745227, 0.657157, 0.553604}
:[font = section; inactive; startGroup; backColorRed = 65280; backColorGreen = 65280; backColorBlue = 65280; fontColorRed = 0; fontColorGreen = 0; fontColorBlue = 0; bold; fontName = "Arial"; fontSize = 14; ]
Parabolic Problem (Nb7d)
:[font = subsection; inactive; startGroup; backColorRed = 65280; backColorGreen = 65280; backColorBlue = 65280; fontColorRed = 0; fontColorGreen = 0; fontColorBlue = 0; bold; fontName = "Arial"; fontSize = 12; ]
Definition
:[font = input; startGroup; nowordwrap; backColorRed = 65280; backColorGreen = 65280; backColorBlue = 65280; fontColorRed = 0; fontColorGreen = 0; fontColorBlue = 0; bold; fontName = "Courier New"; fontSize = 12; ]
g=1; bi=5;
eqgov=(D[u[x,t],t]==D[u[x,t],x,x]+g)

eqicbc={ u[x,0]==0
	,D[u[x,t],x]==0 /. x->0
	,D[u[x,t],x] + bi u[x,t]==0 /. x->1 }
:[font = output; inactive; formatted; output; nowordwrap; ]
Derivative[0, 1][u][x, t] == 1 + Derivative[2, 0][u][x, t]



;[o]
 (0,1)               (2,0)
u     [x, t] == 1 + u     [x, t]
:[font = output; inactive; formatted; output; endGroup; endGroup; nowordwrap; ]
{u[x, 0] == 0, Derivative[1, 0][u][0, t] == 0, 
  5*u[1, t] + Derivative[1, 0][u][1, t] == 0}



;[o]
                (1,0)                          (1,0)
{u[x, 0] == 0, u     [0, t] == 0, 5 u[1, t] + u     [1, t] == 0}
:[font = subsection; inactive; startGroup; backColorRed = 65280; backColorGreen = 65280; backColorBlue = 65280; fontColorRed = 0; fontColorGreen = 0; fontColorBlue = 0; bold; fontName = "Arial"; fontSize = 12; ]
Solution
:[font = input; startGroup; nowordwrap; backColorRed = 65280; backColorGreen = 65280; backColorBlue = 65280; fontColorRed = 0; fontColorGreen = 0; fontColorBlue = 0; bold; fontName = "Courier New"; fontSize = 12; ]
sol=GITT[eqgov,eqicbc,u[x,t],5,t,{{x,0,1}},g (1/2+1/bi-x^2/2),
	mi,qsi,gama,WorkingPrecision->10];
anasol=Chop[sol[[1]] /.
	First[DSolve[Join[sol[[2]],sol[[3]]],sol[[4]],t]]]
Table[Evaluate[u[x,0.1] /. anasol],{x,0,1,0.1}]
:[font = print; inactive; formatted; output; nowordwrap; ]
No Input Form Generated


;[o]
Homogeneous Problem:
     (0,1)             (2,0)
{(uH)     [x, t] - (uH)     [x, t] == 0, 
 
        2
  7    x                       (1,0)
 {-- - -- + uH[x, 0] == 0, (uH)     [0, t] == 0, 
  10   2
 
                   (1,0)
  5 uH[1, t] + (uH)     [1, t] == 0}}

Auxiliary Problem:
                2
{-qsi''[x] == mi  qsi[x], {qsi'[0] == 0, 5 qsi[1] + qsi'[1] == 0}}

EigenValues:
{1.31384, 4.03357, 6.9096, 9.89275, 12.9352}

Normalized EigenFunction:
{1.298 Cos[1.31384 x], 1.33562 Cos[4.03357 x], 1.36798 Cos[6.9096 x], 
 
 1.38629 Cos[9.89275 x], 1.39618 Cos[12.9352 x]}

Transformed ODE System:
  2
mi  gama[t] + gama'[t] == 0

 7 defIntegral[qsi[x], {x, 0, 1}]
{-------------------------------- - 
                10
 
                2
   defIntegral[x  qsi[x], {x, 0, 1}]
   --------------------------------- + gama[0] == 0}
                   2

:[font = output; inactive; formatted; output; nowordwrap; ]
u[x_, t_] -> 7/10 - x^2/2 - 
   (0.7184979669949264*Cos[1.313837716419015*x])/
    E^(1.726169545085131*t) + 
   (0.02115685056902429*Cos[4.033567790334875*x])/
    E^(16.26966911922696*t) - 
   (0.003325660830765811*Cos[6.90959582727156*x])/
    E^(47.74251449624856*t) + 
   (0.000895382131390834*Cos[9.89275256443986*x])/
    E^(97.8665533012315*t) - 
   (0.0003247281446706009*Cos[12.935221287749*x])/
    E^(167.3199497630349*t)



;[o]
                   2
             7    x    0.718498 Cos[1.31384 x]
u[x_, t_] -> -- - -- - ----------------------- + 
             10   2           1.72617 t
                             E
 
  0.0211569 Cos[4.03357 x]   0.00332566 Cos[6.9096 x]
  ------------------------ - ------------------------ + 
          16.2697 t                  47.7425 t
         E                          E
 
  0.000895382 Cos[9.89275 x]   0.000324728 Cos[12.9352 x]
  -------------------------- - --------------------------
           97.8666 t                    167.32 t
          E                            E
:[font = output; inactive; formatted; output; endGroup; endGroup; endGroup; nowordwrap; ]
{0.0995426055209843, 0.0994259497004713, 0.0990367887909314, 
  0.0982518318458749, 0.0968473063533283, 0.0944741932683637, 
  0.0906289846616101, 0.0846253579435115, 0.07557312996309129, 
  0.06237081251214239, 0.04371668010320463}



;[o]
{0.0995426, 0.0994259, 0.0990368, 0.0982518, 0.0968473, 0.0944742, 
 
 0.090629, 0.0846254, 0.0755731, 0.0623708, 0.0437167}
:[font = section; inactive; startGroup; ]
Elliptic Problem
:[font = subsection; inactive; startGroup; backColorRed = 65280; backColorGreen = 65280; backColorBlue = 65280; fontColorRed = 0; fontColorGreen = 0; fontColorBlue = 0; bold; fontName = "Arial"; fontSize = 12; ]
Definition
:[font = input; startGroup; nowordwrap; ]
eqgov=(D[u[x,t],t,t]==D[u[x,t],x,x])

eqicbc={ u[x,0]==-1
	,u[x,1]==-1
	,D[u[x,t],x]==0 /. x->0
	,u[x,t]==0      /. x->1 }
:[font = output; inactive; formatted; output; nowordwrap; ]
Derivative[0, 2][u][x, t] == Derivative[2, 0][u][x, t]



;[o]
 (0,2)           (2,0)
u     [x, t] == u     [x, t]
:[font = output; inactive; formatted; output; endGroup; endGroup; nowordwrap; ]
{u[x, 0] == -1, u[x, 1] == -1, Derivative[1, 0][u][0, t] == 0, 
  u[1, t] == 0}



;[o]
                                (1,0)
{u[x, 0] == -1, u[x, 1] == -1, u     [0, t] == 0, u[1, t] == 0}
:[font = subsection; inactive; startGroup; backColorRed = 65280; backColorGreen = 65280; backColorBlue = 65280; fontColorRed = 0; fontColorGreen = 0; fontColorBlue = 0; bold; fontName = "Arial"; fontSize = 12; ]
Solution
:[font = input; startGroup; Cclosed; nowordwrap; ]
sol=GITT[eqgov,eqicbc,u[x,t],2,t,{{x,0,1}},0,
	mi,qsi,gama,WorkingPrecision->10];
anasol=Simplify[ComplexToTrig[Chop[sol[[1]] /.
	First[DSolve[Join[sol[[2]],sol[[3]]],sol[[4]],t]]]]];
Plot3D[Evaluate[u[x,t] /. anasol],{x,0,1},{t,0,1}
	,AxesLabel->{"x","t","u"}];
:[font = print; inactive; formatted; output; nowordwrap; ]
No Input Form Generated


;[o]
Auxiliary Problem:
                2
{-qsi''[x] == mi  qsi[x], {qsi'[0] == 0, qsi[1] == 0}}

EigenValues:
{1.5708, 4.71239}

Normalized EigenFunction:
{1.41421 Cos[1.5708 x], 1.41421 Cos[4.71239 x]}

Transformed ODE System:
  2
mi  gama[t] + gama''[t] == 0

{gama[0] == -defIntegral[qsi[x], {x, 0, 1}], 
 
 gama[1] == -defIntegral[qsi[x], {x, 0, 1}]}

:[font = postscript; inactive; output; endGroup; endGroup; endGroup; BITMAP; PostScript; pictureLeft = 0; pictureTop = 0; pictureWidth = 500; pictureHeight = 410; nowordwrap; ]
%!
%%Creator: Mathematica
%%AspectRatio: .82055 
MathPictureStart
%% SurfaceGraphics
/Courier findfont 10  scalefont  setfont
% Scaling calculations
0.0249355 0.99742 -0.0396341 0.99742 [
[(0)] .05113 .25884 1 .93395 Msboxa
[(0.2)] .16364 .21456 .98733 1 Msboxa
[(0.4)] .2816 .16815 .90393 1 Msboxa
[(0.6)] .40542 .11945 .82054 1 Msboxa
[(0.8)] .53556 .0683 .73714 1 Msboxa
[(1)] .6725 .0145 .65374 1 Msboxa
[(x)] .30204 .09689 .86223 1 Msboxa
[(0)] .69093 .02039 -1 .39157 Msboxa
[(0.2)] .75411 .11713 -1 .3693 Msboxa
[(0.4)] .81175 .20539 -1 .34944 Msboxa
[(0.6)] .86455 .28624 -1 .3316 Msboxa
[(0.8)] .9131 .36059 -1 .31549 Msboxa
[(1)] .95788 .42917 -1 .30087 Msboxa
[(t)] .89773 .2266 -1 .34028 Msboxa
[(-2)] .04253 .31016 1 -0.38401 Msboxa
[(-1)] .02871 .39675 1 -0.36683 Msboxa
[(0)] .01407 .48855 1 -0.3485 Msboxa
[(u)] -0.02691 .40064 1 -0.37036 Msboxa
[ 0 0 0 0 ]
[ 1 .82055 0 0 ]
] MathScale
% Start of Graphics
1 setlinecap
1 setlinejoin
newpath
[ ] 0 setdash
0 g
p
p
.002 w
.06024 .26735 m
.67932 .02494 L
s
P
p
.002 w
.06024 .26735 m
.0648 .2716 L
s
P
[(0)] .05113 .25884 1 .93395 Mshowa
p
.002 w
.17239 .22343 m
.17677 .22787 L
s
P
[(0.2)] .16364 .21456 .98733 1 Mshowa
p
.002 w
.28996 .1774 m
.29414 .18202 L
s
P
[(0.4)] .2816 .16815 .90393 1 Mshowa
p
.002 w
.41333 .12909 m
.41729 .13391 L
s
P
[(0.6)] .40542 .11945 .82054 1 Mshowa
p
.002 w
.54296 .07833 m
.54666 .08335 L
s
P
[(0.8)] .53556 .0683 .73714 1 Mshowa
p
.002 w
.67932 .02494 m
.68274 .03015 L
s
P
[(1)] .6725 .0145 .65374 1 Mshowa
p
.001 w
.08226 .25873 m
.08497 .2613 L
s
P
p
.001 w
.10448 .25003 m
.10717 .25262 L
s
P
p
.001 w
.12691 .24125 m
.12958 .24386 L
s
P
p
.001 w
.14954 .23238 m
.15219 .23502 L
s
P
p
.001 w
.19546 .2144 m
.19807 .21708 L
s
P
p
.001 w
.21875 .20528 m
.22133 .20799 L
s
P
p
.001 w
.24226 .19608 m
.24482 .19881 L
s
P
p
.001 w
.26599 .18678 m
.26853 .18953 L
s
P
p
.001 w
.31415 .16792 m
.31664 .17072 L
s
P
p
.001 w
.33859 .15836 m
.34104 .16118 L
s
P
p
.001 w
.36326 .1487 m
.36569 .15154 L
s
P
p
.001 w
.38817 .13894 m
.39057 .14181 L
s
P
p
.001 w
.43874 .11914 m
.44108 .12206 L
s
P
p
.001 w
.4644 .10909 m
.46672 .11203 L
s
P
p
.001 w
.49033 .09894 m
.49261 .1019 L
s
P
p
.001 w
.51651 .08869 m
.51876 .09168 L
s
P
p
.001 w
.56967 .06787 m
.57186 .07091 L
s
P
p
.001 w
.59667 .0573 m
.59882 .06036 L
s
P
p
.001 w
.62394 .04662 m
.62605 .04971 L
s
P
p
.001 w
.65149 .03584 m
.65357 .03894 L
s
P
[(x)] .30204 .09689 .86223 1 Mshowa
P
p
p
.002 w
.67932 .02494 m
.94594 .43277 L
s
P
p
.002 w
.67932 .02494 m
.67352 .02721 L
s
P
[(0)] .69093 .02039 -1 .39157 Mshowa
p
.002 w
.74242 .12145 m
.73657 .1236 L
s
P
[(0.2)] .75411 .11713 -1 .3693 Mshowa
p
.002 w
.79998 .2095 m
.7941 .21156 L
s
P
[(0.4)] .81175 .20539 -1 .34944 Mshowa
p
.002 w
.85272 .29017 m
.8468 .29213 L
s
P
[(0.6)] .86455 .28624 -1 .3316 Mshowa
p
.002 w
.90121 .36434 m
.89526 .36621 L
s
P
[(0.8)] .9131 .36059 -1 .31549 Mshowa
p
.002 w
.94594 .43277 m
.93997 .43456 L
s
P
[(1)] .95788 .42917 -1 .30087 Mshowa
p
.001 w
.69242 .04497 m
.68893 .04632 L
s
P
p
.001 w
.70527 .06463 m
.70178 .06597 L
s
P
p
.001 w
.71789 .08392 m
.71439 .08524 L
s
P
p
.001 w
.73026 .10286 m
.72676 .10417 L
s
P
p
.001 w
.75435 .1397 m
.75083 .14098 L
s
P
p
.001 w
.76606 .15762 m
.76255 .15889 L
s
P
p
.001 w
.77757 .17522 m
.77405 .17648 L
s
P
p
.001 w
.78888 .19251 m
.78535 .19376 L
s
P
p
.001 w
.8109 .2262 m
.80736 .22742 L
s
P
p
.001 w
.82162 .2426 m
.81808 .24381 L
s
P
p
.001 w
.83216 .25873 m
.82862 .25993 L
s
P
p
.001 w
.84253 .27458 m
.83898 .27577 L
s
P
p
.001 w
.86274 .3055 m
.85918 .30666 L
s
P
p
.001 w
.87259 .32057 m
.86904 .32173 L
s
P
p
.001 w
.88229 .3354 m
.87873 .33654 L
s
P
p
.001 w
.89182 .34999 m
.88826 .35112 L
s
P
p
.001 w
.91044 .37846 m
.90687 .37958 L
s
P
p
.001 w
.91953 .39236 m
.91595 .39347 L
s
P
p
.001 w
.92847 .40604 m
.92489 .40714 L
s
P
p
.001 w
.93727 .41951 m
.93369 .4206 L
s
P
[(t)] .89773 .2266 -1 .34028 Mshowa
P
p
p
.002 w
.06024 .26735 m
.02494 .49015 L
s
P
p
.002 w
.05417 .30569 m
.05999 .30346 L
s
P
[(-2)] .04253 .31016 1 -0.38401 Mshowa
p
.002 w
.04042 .39245 m
.04627 .39031 L
s
P
[(-1)] .02871 .39675 1 -0.36683 Mshowa
p
.002 w
.02584 .48445 m
.03173 .4824 L
s
P
[(0)] .01407 .48855 1 -0.3485 Mshowa
p
.001 w
.05148 .32265 m
.05497 .32132 L
s
P
p
.001 w
.04876 .3398 m
.05226 .33848 L
s
P
p
.001 w
.04601 .35715 m
.04952 .35584 L
s
P
p
.001 w
.04323 .3747 m
.04674 .3734 L
s
P
p
.001 w
.03757 .41042 m
.04109 .40914 L
s
P
p
.001 w
.03469 .4286 m
.03821 .42733 L
s
P
p
.001 w
.03177 .44699 m
.0353 .44574 L
s
P
p
.001 w
.02882 .46561 m
.03235 .46436 L
s
P
p
.001 w
.05682 .28893 m
.06031 .28758 L
s
P
p
.001 w
.05945 .27236 m
.06293 .27099 L
s
P
[(u)] -0.02691 .40064 1 -0.37036 Mshowa
P
0 0 m
1 0 L
1 .82055 L
0 .82055 L
closepath
clip
newpath
p
.002 w
.06024 .26735 m
.02494 .49015 L
s
.02494 .49015 m
.40296 .79562 L
s
.40296 .79562 m
.41001 .59401 L
s
.41001 .59401 m
.06024 .26735 L
s
.67932 .02494 m
.94594 .43277 L
s
.94594 .43277 m
.97506 .64585 L
s
.97506 .64585 m
.69286 .25814 L
s
.69286 .25814 m
.67932 .02494 L
s
.06024 .26735 m
.02494 .49015 L
s
.02494 .49015 m
.69286 .25814 L
s
.69286 .25814 m
.67932 .02494 L
s
.67932 .02494 m
.06024 .26735 L
s
.41001 .59401 m
.94594 .43277 L
s
.94594 .43277 m
.97506 .64585 L
s
.97506 .64585 m
.40296 .79562 L
s
.40296 .79562 m
.41001 .59401 L
s
P
p
.645 .594 .783 r
.0015 w
.38487 .67725 .4056 .72012 .44185 .70881 .42116 .66641 Metetra
.651 .6 .784 r
.42116 .66641 .44185 .70881 .47862 .69499 .45799 .6546 Metetra
.656 .611 .793 r
.45799 .6546 .47862 .69499 .51584 .67922 .49532 .64218 Metetra
.659 .629 .809 r
.49532 .64218 .51584 .67922 .55347 .66244 .53315 .62968 Metetra
.659 .653 .833 r
.53315 .62968 .55347 .66244 .5915 .6458 .57151 .61778 Metetra
.651 .683 .867 r
.57151 .61778 .5915 .6458 .63 .63052 .61046 .60722 Metetra
.63 .716 .909 r
.61046 .60722 .63 .63052 .66909 .61778 .65009 .5987 Metetra
.585 .744 .952 r
.65009 .5987 .66909 .61778 .70892 .60858 .69052 .5928 Metetra
.51 .755 .984 r
.69052 .5928 .70892 .60858 .7497 .60362 .73191 .58993 Metetra
.413 .737 .992 r
.73191 .58993 .7497 .60362 .79164 .60327 .77442 .59028 Metetra
.325 .699 .981 r
.77442 .59028 .79164 .60327 .83494 .60745 .81819 .59376 Metetra
.277 .662 .97 r
.81819 .59376 .83494 .60745 .87978 .61569 .86335 .6 Metetra
.277 .638 .965 r
.86335 .6 .87978 .61569 .92624 .6271 .90998 .6084 Metetra
.313 .624 .959 r
.90998 .6084 .92624 .6271 .97432 .64043 .95811 .61809 Metetra
.639 .588 .781 r
.36393 .63297 .38487 .67725 .42116 .66641 .40025 .62268 Metetra
.634 .589 .786 r
.40025 .62268 .42116 .66641 .45799 .6546 .43708 .61321 Metetra
.63 .598 .799 r
.43708 .61321 .45799 .6546 .49532 .64218 .47446 .60463 Metetra
.624 .614 .82 r
.47446 .60463 .49532 .64218 .53315 .62968 .51245 .59706 Metetra
.615 .639 .852 r
.51245 .59706 .53315 .62968 .57151 .61778 .55109 .59064 Metetra
.597 .673 .893 r
.55109 .59064 .57151 .61778 .61046 .60722 .59046 .58553 Metetra
.562 .711 .941 r
.59046 .58553 .61046 .60722 .65009 .5987 .63063 .58184 Metetra
.502 .742 .981 r
.63063 .58184 .65009 .5987 .69052 .5928 .67169 .57968 Metetra
.416 .749 .994 r
.67169 .57968 .69052 .5928 .73191 .58993 .71373 .57907 Metetra
.328 .731 .981 r
.71373 .57907 .73191 .58993 .77442 .59028 .75683 .57997 Metetra
.276 .708 .966 r
.75683 .57997 .77442 .59028 .81819 .59376 .80109 .58227 Metetra
.276 .695 .969 r
.80109 .58227 .81819 .59376 .86335 .6 .84656 .58576 Metetra
.319 .688 .979 r
.84656 .58576 .86335 .6 .90998 .6084 .89333 .59015 Metetra
.379 .676 .975 r
.89333 .59015 .90998 .6084 .95811 .61809 .94141 .59508 Metetra
.634 .589 .786 r
.34271 .5891 .36393 .63297 .40025 .62268 .37905 .57938 Metetra
.617 .584 .794 r
.37905 .57938 .40025 .62268 .43708 .61321 .41585 .57227 Metetra
.6 .588 .811 r
.41585 .57227 .43708 .61321 .47446 .60463 .45324 .5676 Metetra
.581 .6 .837 r
.45324 .5676 .47446 .60463 .51245 .59706 .49131 .56506 Metetra
.556 .622 .873 r
.49131 .56506 .51245 .59706 .55109 .59064 .53018 .56427 Metetra
.521 .652 .917 r
.53018 .56427 .55109 .59064 .59046 .58553 .56993 .56476 Metetra
.47 .687 .961 r
.56993 .56476 .59046 .58553 .63063 .58184 .61061 .56606 Metetra
.399 .712 .986 r
.61061 .56606 .63063 .58184 .67169 .57968 .65229 .56771 Metetra
.325 .72 .981 r
.65229 .56771 .67169 .57968 .71373 .57907 .69497 .56935 Metetra
.276 .717 .963 r
.69497 .56935 .71373 .57907 .75683 .57997 .73869 .57066 Metetra
.276 .723 .96 r
.73869 .57066 .75683 .57997 .80109 .58227 .78345 .5715 Metetra
.324 .737 .978 r
.78345 .5715 .80109 .58227 .84656 .58576 .82926 .57182 Metetra
.395 .742 .992 r
.82926 .57182 .84656 .58576 .89333 .59015 .87616 .57171 Metetra
.46 .726 .983 r
.87616 .57171 .89333 .59015 .94141 .59508 .92419 .57135 Metetra
.631 .599 .799 r
.32106 .54751 .34271 .5891 .37905 .57938 .35743 .53827 Metetra
.6 .588 .811 r
.35743 .53827 .37905 .57938 .41585 .57227 .39421 .53327 Metetra
.566 .584 .83 r
.39421 .53327 .41585 .57227 .45324 .5676 .43158 .53213 Metetra
.527 .587 .858 r
.43158 .53213 .45324 .5676 .49131 .56506 .46971 .53418 Metetra
.482 .6 .894 r
.46971 .53418 .49131 .56506 .53018 .56427 .50875 .53853 Metetra
.427 .619 .932 r
.50875 .53853 .53018 .56427 .56993 .56476 .54881 .54418 Metetra
.365 .643 .962 r
.54881 .54418 .56993 .56476 .61061 .56606 .58995 .55008 Metetra
.305 .666 .974 r
.58995 .55008 .61061 .56606 .65229 .56771 .63218 .55526 Metetra
.269 .687 .968 r
.63218 .55526 .65229 .56771 .69497 .56935 .67549 .5589 Metetra
.275 .713 .964 r
.67549 .5589 .69497 .56935 .73869 .57066 .71982 .56048 Metetra
.326 .747 .975 r
.71982 .56048 .73869 .57066 .78345 .5715 .7651 .55977 Metetra
.404 .777 .993 r
.7651 .55977 .78345 .5715 .82926 .57182 .81129 .55693 Metetra
.481 .783 .998 r
.81129 .55693 .82926 .57182 .87616 .57171 .85838 .55239 Metetra
.536 .762 .98 r
.85838 .55239 .87616 .57171 .92419 .57135 .90643 .54688 Metetra
.629 .619 .821 r
.29879 .50984 .32106 .54751 .35743 .53827 .33525 .50091 Metetra
.582 .601 .837 r
.33525 .50091 .35743 .53827 .39421 .53327 .37204 .49754 Metetra
.527 .587 .859 r
.37204 .49754 .39421 .53327 .43158 .53213 .40941 .49917 Metetra
.465 .578 .884 r
.40941 .49917 .43158 .53213 .46971 .53418 .44757 .50483 Metetra
.397 .575 .91 r
.44757 .50483 .46971 .53418 .50875 .53853 .48674 .51329 Metetra
.329 .58 .933 r
.48674 .51329 .50875 .53853 .54881 .54418 .52705 .52308 Metetra
.274 .594 .949 r
.52705 .52308 .54881 .54418 .58995 .55008 .56857 .53269 Metetra
.248 .622 .958 r
.56857 .53269 .58995 .55008 .63218 .55526 .6113 .54068 Metetra
.263 .664 .967 r
.6113 .54068 .63218 .55526 .67549 .5589 .65518 .54589 Metetra
.318 .716 .98 r
.65518 .54589 .67549 .5589 .71982 .56048 .70008 .54757 Metetra
.401 .765 .994 r
.70008 .54757 .71982 .56048 .7651 .55977 .74589 .54547 Metetra
.487 .796 .999 r
.74589 .54547 .7651 .55977 .81129 .55693 .79251 .53986 Metetra
.555 .799 .99 r
.79251 .53986 .81129 .55693 .85838 .55239 .8399 .53153 Metetra
.594 .779 .968 r
.8399 .53153 .85838 .55239 .90643 .54688 .88811 .52163 Metetra
.628 .652 .855 r
.27568 .47741 .29879 .50984 .33525 .50091 .3123 .46857 Metetra
.562 .628 .875 r
.3123 .46857 .33525 .50091 .37204 .49754 .34917 .46614 Metetra
.483 .602 .895 r
.34917 .46614 .37204 .49754 .40941 .49917 .38659 .46946 Metetra
.396 .575 .91 r
.38659 .46946 .40941 .49917 .44757 .50483 .42482 .47739 Metetra
.313 .553 .92 r
.42482 .47739 .44757 .50483 .48674 .51329 .46412 .48844 Metetra
.249 .545 .926 r
.46412 .48844 .48674 .51329 .52705 .52308 .50464 .50087 Metetra
.221 .558 .935 r
.50464 .50087 .52705 .52308 .56857 .53269 .54647 .51282 Metetra
.237 .595 .949 r
.54647 .51282 .56857 .53269 .6113 .54068 .58961 .52257 Metetra
.294 .65 .969 r
.58961 .52257 .6113 .54068 .65518 .54589 .63398 .52872 Metetra
.38 .71 .986 r
.63398 .52872 .65518 .54589 .70008 .54757 .67941 .53034 Metetra
.471 .758 .993 r
.67941 .53034 .70008 .54757 .74589 .54547 .72574 .52716 Metetra
.549 .786 .987 r
.72574 .52716 .74589 .54547 .79251 .53986 .77285 .51956 Metetra
.602 .791 .972 r
.77285 .51956 .79251 .53986 .8399 .53153 .82065 .50854 Metetra
.629 .78 .954 r
.82065 .50854 .8399 .53153 .88811 .52163 .86919 .49556 Metetra
.627 .701 .899 r
.2515 .4511 .27568 .47741 .3123 .46857 .28836 .44207 Metetra
.54 .67 .922 r
.28836 .44207 .3123 .46857 .34917 .46614 .32542 .43978 Metetra
.435 .628 .935 r
.32542 .43978 .34917 .46614 .38659 .46946 .36299 .44352 Metetra
.331 .582 .934 r
.36299 .44352 .38659 .46946 .42482 .47739 .40137 .45209 Metetra
.248 .545 .926 r
.40137 .45209 .42482 .47739 .46412 .48844 .44082 .4639 Metetra
.207 .531 .922 r
.44082 .4639 .46412 .48844 .50464 .50087 .48155 .47711 Metetra
.215 .545 .929 r
.48155 .47711 .50464 .50087 .54647 .51282 .52365 .48974 Metetra
.265 .584 .945 r
.52365 .48974 .54647 .51282 .58961 .52257 .56712 .49996 Metetra
.345 .637 .962 r
.56712 .49996 .58961 .52257 .63398 .52872 .61189 .50625 Metetra
.435 .689 .971 r
.61189 .50625 .63398 .52872 .67941 .53034 .65778 .50764 Metetra
.517 .73 .97 r
.65778 .50764 .67941 .53034 .72574 .52716 .70462 .50384 Metetra
.58 .756 .961 r
.70462 .50384 .72574 .52716 .77285 .51956 .75224 .49527 Metetra
.621 .768 .95 r
.75224 .49527 .77285 .51956 .82065 .50854 .80058 .48301 Metetra
.642 .769 .94 r
.80058 .48301 .82065 .50854 .86919 .49556 .84965 .46863 Metetra
.62 .763 .948 r
.22601 .43127 .2515 .4511 .28836 .44207 .26322 .42177 Metetra
.513 .726 .97 r
.26322 .42177 .28836 .44207 .32542 .43978 .30061 .41876 Metetra
.391 .668 .97 r
.30061 .41876 .32542 .43978 .36299 .44352 .33847 .42156 Metetra
.286 .606 .953 r
.33847 .42156 .36299 .44352 .40137 .45209 .37711 .42902 Metetra
.225 .561 .936 r
.37711 .42902 .40137 .45209 .44082 .4639 .41681 .43963 Metetra
.215 .545 .929 r
.41681 .43963 .44082 .4639 .48155 .47711 .45777 .45162 Metetra
.252 .557 .933 r
.45777 .45162 .48155 .47711 .52365 .48974 .50012 .46313 Metetra
.319 .587 .94 r
.50012 .46313 .52365 .48974 .56712 .49996 .54387 .47239 Metetra
.397 .624 .944 r
.54387 .47239 .56712 .49996 .61189 .50625 .58895 .47798 Metetra
.473 .661 .943 r
.58895 .47798 .61189 .50625 .65778 .50764 .63523 .47897 Metetra
.538 .692 .939 r
.63523 .47897 .65778 .50764 .70462 .50384 .68253 .47506 Metetra
.587 .717 .933 r
.68253 .47506 .70462 .50384 .75224 .49527 .73071 .46664 Metetra
.619 .736 .93 r
.73071 .46664 .75224 .49527 .80058 .48301 .77968 .45473 Metetra
.635 .75 .931 r
.77968 .45473 .80058 .48301 .84965 .46863 .82945 .44081 Metetra
.6 .828 .987 r
.19901 .41777 .22601 .43127 .26322 .42177 .23669 .40753 Metetra
.482 .784 .998 r
.23669 .40753 .26322 .42177 .30061 .41876 .27455 .40296 Metetra
.365 .717 .987 r
.27455 .40296 .30061 .41876 .33847 .42156 .31287 .40349 Metetra
.284 .653 .969 r
.31287 .40349 .33847 .42156 .37711 .42902 .35195 .40814 Metetra
.254 .608 .955 r
.35195 .40814 .37711 .42902 .41681 .43963 .39202 .41564 Metetra
.271 .588 .946 r
.39202 .41564 .41681 .43963 .45777 .45162 .43331 .42449 Metetra
.32 .588 .94 r
.43331 .42449 .45777 .45162 .50012 .46313 .47592 .43312 Metetra
.381 .598 .932 r
.47592 .43312 .50012 .46313 .54387 .47239 .51992 .44007 Metetra
.443 .615 .923 r
.51992 .44007 .54387 .47239 .58895 .47798 .56526 .44413 Metetra
.497 .634 .914 r
.56526 .44413 .58895 .47798 .63523 .47897 .61185 .44453 Metetra
.542 .656 .909 r
.61185 .44453 .63523 .47897 .68253 .47506 .65956 .44098 Metetra
.577 .678 .909 r
.65956 .44098 .68253 .47506 .73071 .46664 .70828 .43379 Metetra
.6 .702 .915 r
.70828 .43379 .73071 .46664 .77968 .45473 .75795 .42374 Metetra
.611 .725 .926 r
.75795 .42374 .77968 .45473 .82945 .44081 .80857 .41203 Metetra
.563 .875 .994 r
.17034 .40992 .19901 .41777 .23669 .40753 .20859 .39867 Metetra
.458 .829 .992 r
.20859 .39867 .23669 .40753 .27455 .40296 .24709 .3918 Metetra
.374 .772 .986 r
.24709 .3918 .27455 .40296 .31287 .40349 .28608 .3889 Metetra
.333 .721 .983 r
.28608 .3889 .31287 .40349 .35195 .40814 .32578 .38927 Metetra
.334 .68 .978 r
.32578 .38927 .35195 .40814 .39202 .41564 .3664 .392 Metetra
.362 .649 .965 r
.3664 .392 .39202 .41564 .43331 .42449 .40812 .39604 Metetra
.403 .628 .945 r
.40812 .39604 .43331 .42449 .47592 .43312 .45107 .40031 Metetra
.444 .615 .922 r
.45107 .40031 .47592 .43312 .51992 .44007 .49532 .40378 Metetra
.48 .611 .904 r
.49532 .40378 .51992 .44007 .56526 .44413 .54088 .4056 Metetra
.512 .615 .892 r
.54088 .4056 .56526 .44413 .61185 .44453 .58773 .40522 Metetra
.537 .626 .888 r
.58773 .40522 .61185 .44453 .65956 .44098 .6358 .40239 Metetra
.557 .644 .892 r
.6358 .40239 .65956 .44098 .70828 .43379 .68503 .39727 Metetra
.569 .668 .905 r
.68503 .39727 .70828 .43379 .75795 .42374 .73541 .39031 Metetra
.572 .696 .925 r
.73541 .39031 .75795 .42374 .80857 .41203 .78697 .38226 Metetra
.522 .893 .969 r
.13989 .40653 .17034 .40992 .20859 .39867 .17882 .39409 Metetra
.457 .86 .966 r
.17882 .39409 .20859 .39867 .24709 .3918 .21814 .38434 Metetra
.425 .829 .978 r
.21814 .38434 .24709 .3918 .28608 .3889 .25798 .37711 Metetra
.426 .797 .994 r
.25798 .37711 .28608 .3889 .32578 .38927 .2985 .37207 Metetra
.445 .758 .995 r
.2985 .37207 .32578 .38927 .3664 .392 .33985 .3688 Metetra
.467 .712 .975 r
.33985 .3688 .3664 .392 .40812 .39604 .38216 .36684 Metetra
.486 .669 .944 r
.38216 .36684 .40812 .39604 .45107 .40031 .42555 .36566 Metetra
.501 .636 .914 r
.42555 .36566 .45107 .40031 .49532 .40378 .4701 .36481 Metetra
.512 .615 .892 r
.4701 .36481 .49532 .40378 .54088 .4056 .51589 .36385 Metetra
.52 .606 .879 r
.51589 .36385 .54088 .4056 .58773 .40522 .56295 .3625 Metetra
.526 .606 .876 r
.56295 .3625 .58773 .40522 .6358 .40239 .61132 .36056 Metetra
.529 .617 .884 r
.61132 .36056 .6358 .40239 .68503 .39727 .66103 .35799 Metetra
.528 .636 .901 r
.66103 .35799 .68503 .39727 .73541 .39031 .7121 .35489 Metetra
.521 .663 .925 r
.7121 .35489 .73541 .39031 .78697 .38226 .7646 .35145 Metetra
.501 .897 .941 r
.10766 .40603 .13989 .40653 .17882 .39409 .14736 .39226 Metetra
.49 .888 .948 r
.14736 .39226 .17882 .39409 .21814 .38434 .18762 .37929 Metetra
.507 .882 .973 r
.18762 .37929 .21814 .38434 .25798 .37711 .2285 .3672 Metetra
.535 .862 .995 r
.2285 .3672 .25798 .37711 .2985 .37207 .27003 .35612 Metetra
.558 .821 .995 r
.27003 .35612 .2985 .37207 .33985 .3688 .3123 .34619 Metetra
.566 .765 .972 r
.3123 .34619 .33985 .3688 .38216 .36684 .35536 .33757 Metetra
.562 .709 .94 r
.35536 .33757 .38216 .36684 .42555 .36566 .39931 .3304 Metetra
.552 .663 .91 r
.39931 .3304 .42555 .36566 .4701 .36481 .44425 .32477 Metetra
.54 .628 .888 r
.44425 .32477 .4701 .36481 .51589 .36385 .49029 .32071 Metetra
.527 .606 .876 r
.49029 .32071 .51589 .36385 .56295 .3625 .53757 .31819 Metetra
.513 .596 .875 r
.53757 .31819 .56295 .3625 .61132 .36056 .58621 .31708 Metetra
.498 .597 .883 r
.58621 .31708 .61132 .36056 .66103 .35799 .63633 .31715 Metetra
.481 .608 .901 r
.63633 .31715 .66103 .35799 .7121 .35489 .68804 .31809 Metetra
.46 .628 .926 r
.68804 .31809 .7121 .35489 .7646 .35145 .74143 .31952 Metetra
.512 .905 .934 r
.07373 .40653 .10766 .40603 .14736 .39226 .11425 .3914 Metetra
.549 .917 .949 r
.11425 .3914 .14736 .39226 .18762 .37929 .15556 .37514 Metetra
.596 .92 .971 r
.15556 .37514 .18762 .37929 .2285 .3672 .1976 .35812 Metetra
.634 .902 .985 r
.1976 .35812 .2285 .3672 .27003 .35612 .2403 .34092 Metetra
.65 .86 .979 r
.2403 .34092 .27003 .35612 .3123 .34619 .28363 .32429 Metetra
.645 .804 .959 r
.28363 .32429 .3123 .34619 .35536 .33757 .32759 .30901 Metetra
.625 .746 .934 r
.32759 .30901 .35536 .33757 .39931 .3304 .37223 .29583 Metetra
.597 .694 .911 r
.37223 .29583 .39931 .3304 .44425 .32477 .41766 .28539 Metetra
.565 .651 .894 r
.41766 .28539 .44425 .32477 .49029 .32071 .46403 .27814 Metetra
.532 .619 .884 r
.46403 .27814 .49029 .32071 .53757 .31819 .51156 .27426 Metetra
.498 .597 .883 r
.51156 .27426 .53757 .31819 .58621 .31708 .56046 .27368 Metetra
.464 .586 .891 r
.56046 .27368 .58621 .31708 .63633 .31715 .61094 .276 Metetra
.429 .585 .905 r
.61094 .276 .63633 .31715 .68804 .31809 .66322 .28056 Metetra
.396 .595 .925 r
.66322 .28056 .68804 .31809 .74143 .31952 .71742 .28643 Metetra
.55 .917 .949 r
.03827 .40601 .07373 .40653 .11425 .3914 .07963 .3896 Metetra
.617 .936 .959 r
.07963 .3896 .11425 .3914 .15556 .37514 .12203 .37028 Metetra
.672 .937 .967 r
.12203 .37028 .15556 .37514 .1976 .35812 .16529 .34872 Metetra
.706 .916 .966 r
.16529 .34872 .1976 .35812 .2403 .34092 .20924 .32594 Metetra
.715 .879 .957 r
.20924 .32594 .2403 .34092 .28363 .32429 .25374 .30321 Metetra
.702 .831 .944 r
.25374 .30321 .28363 .32429 .32759 .30901 .2987 .28187 Metetra
.674 .78 .93 r
.2987 .28187 .32759 .30901 .37223 .29583 .34415 .26321 Metetra
.635 .73 .917 r
.34415 .26321 .37223 .29583 .41766 .28539 .39018 .24832 Metetra
.588 .684 .908 r
.39018 .24832 .41766 .28539 .46403 .27814 .43699 .23797 Metetra
.536 .644 .903 r
.43699 .23797 .46403 .27814 .51156 .27426 .48483 .23254 Metetra
.483 .61 .902 r
.48483 .23254 .51156 .27426 .56046 .27368 .53402 .23197 Metetra
.429 .585 .905 r
.53402 .23197 .56046 .27368 .61094 .276 .58486 .23575 Metetra
.379 .571 .913 r
.58486 .23575 .61094 .276 .66322 .28056 .63762 .24292 Metetra
.337 .569 .924 r
.63762 .24292 .66322 .28056 .71742 .28643 .69251 .25211 Metetra
P
p
.002 w
.67932 .02494 m
.94594 .43277 L
s
.94594 .43277 m
.97506 .64585 L
s
.97506 .64585 m
.69286 .25814 L
s
.69286 .25814 m
.67932 .02494 L
s
.06024 .26735 m
.02494 .49015 L
s
.02494 .49015 m
.69286 .25814 L
s
.69286 .25814 m
.67932 .02494 L
s
.67932 .02494 m
.06024 .26735 L
s
P
p
p
.002 w
.06024 .26735 m
.67932 .02494 L
s
P
p
.002 w
.06024 .26735 m
.0648 .2716 L
s
P
[(0)] .05113 .25884 1 .93395 Mshowa
p
.002 w
.17239 .22343 m
.17677 .22787 L
s
P
[(0.2)] .16364 .21456 .98733 1 Mshowa
p
.002 w
.28996 .1774 m
.29414 .18202 L
s
P
[(0.4)] .2816 .16815 .90393 1 Mshowa
p
.002 w
.41333 .12909 m
.41729 .13391 L
s
P
[(0.6)] .40542 .11945 .82054 1 Mshowa
p
.002 w
.54296 .07833 m
.54666 .08335 L
s
P
[(0.8)] .53556 .0683 .73714 1 Mshowa
p
.002 w
.67932 .02494 m
.68274 .03015 L
s
P
[(1)] .6725 .0145 .65374 1 Mshowa
p
.001 w
.08226 .25873 m
.08497 .2613 L
s
P
p
.001 w
.10448 .25003 m
.10717 .25262 L
s
P
p
.001 w
.12691 .24125 m
.12958 .24386 L
s
P
p
.001 w
.14954 .23238 m
.15219 .23502 L
s
P
p
.001 w
.19546 .2144 m
.19807 .21708 L
s
P
p
.001 w
.21875 .20528 m
.22133 .20799 L
s
P
p
.001 w
.24226 .19608 m
.24482 .19881 L
s
P
p
.001 w
.26599 .18678 m
.26853 .18953 L
s
P
p
.001 w
.31415 .16792 m
.31664 .17072 L
s
P
p
.001 w
.33859 .15836 m
.34104 .16118 L
s
P
p
.001 w
.36326 .1487 m
.36569 .15154 L
s
P
p
.001 w
.38817 .13894 m
.39057 .14181 L
s
P
p
.001 w
.43874 .11914 m
.44108 .12206 L
s
P
p
.001 w
.4644 .10909 m
.46672 .11203 L
s
P
p
.001 w
.49033 .09894 m
.49261 .1019 L
s
P
p
.001 w
.51651 .08869 m
.51876 .09168 L
s
P
p
.001 w
.56967 .06787 m
.57186 .07091 L
s
P
p
.001 w
.59667 .0573 m
.59882 .06036 L
s
P
p
.001 w
.62394 .04662 m
.62605 .04971 L
s
P
p
.001 w
.65149 .03584 m
.65357 .03894 L
s
P
[(x)] .30204 .09689 .86223 1 Mshowa
P
% End of Graphics
MathPictureEnd
^*)
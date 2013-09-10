This is KleinianGroups, version 1.0 of September 25, 2012.

KleinianGroups is a Magma package computing fundamental domains for arithmetic Kleinian groups.
Copyright (C) 2010-2012  Aurel Page

KleinianGroups is free software: you can redistribute it and/or modify it under the terms of the GNU General Public License as published by the Free Software Foundation, either version 3 of the License, or (at your option) any later version.

KleinianGroups is distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for more details.

You should have received a copy of the GNU General Public License along with this program, in the file COPYING. If not, see <http://www.gnu.org/licenses/>.

======================================================================

To get started, you should first acquire a copy of Magma at

  http://magma.maths.usyd.edu.au/magma/download/all/

The KleinianGroups package is attached with the line

  AttachSpec("KleinianGroups/klngpspec");

with the appropriate modification of the path.
The main intrinsics you can use are :

  NormalizedBasis :
    Input : an order O in a Kleinian quaternion algebra.
    Output : the sequence of generators, the sequence of faces and the sequence of edges of the computed Dirichlet domain for the group G of norm 1 elements in O modulo +-1.
    Parameters : 
        - setting 'Maple := true' will produce three files : 'FinalFDom.mpl', 'FinalFDomS.mpl', 'FinalFDomC.mpl'. They contain Maple code printing the computed fundamental domain. The first one only prints the edges, the second one the edges and faces, the third one the edges with their index in the sequence of edges.
        - GroupType can have the values "NormOne" (default), "Units" or "Maximal" depending on which group you want to compute.

  Presentation :
    Input : the sequence of faces and the sequence of edges returned by NormalizedBasis, and the order O.
    Output : a finitely presented group G isomorphic to the group computed by NormalizedBasis (modulo center), and a sequence of elements of O : the corresponding generators.

  LiftPresentation :
    Input : the finitely presented group and the sequence of generators returned by Presentation, the order O and a boolean indicating whether the group computed is the norm one group or the unit group. 
    Output : a finitely presented group G isomorphic to the group computed by NormalizedBasis, and a sequence of elements of O : the corresponding generators.

  Word :
    Input : an element gamma in an arithmetic group in the order O, the sequence of faces returned by NormalizedBasis, and the finitely presented group G returned by Presentation.
    Output : an element of G corresponding to gamma.

  ReducePoint :
    Input : a point z in the unit ball model of the hyperbolic space and the sequence of faces returned by NormalizedBasis.
    Output : a point z' equivalent to z in the fundamental domain, a sequence of integers representing the indices of the successive faces used for reduction, and the quaternion delta such that z' = delta*z.

See the file 'example.m' for some examples of use. WARNING : the output of the file 'example.m' is nondeterministic, since the construction of the quaternion algebra and of the maximal order are nondeterministic. The groups you will obtain are isomorphic, but the fundamental domains may be distinct.

======================================================================

You can write to me at

  aurel.page@math.u-bordeaux1.fr

Please report any bug you find and send me feedback !

The latest version can be found at

  http://www.normalesup.org/~page/Recherche/Logiciels/logiciels-en.html
  
Thanks for you support, and have fun !

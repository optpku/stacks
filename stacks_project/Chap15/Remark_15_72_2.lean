/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.Monoidal.Closed.ModuleCat
import StacksCheckRecall

/-!
# Closed symmetric structure and the Hom complex

For complexes of modules, the ambient closed internal Hom is naturally isomorphic to the
module-valued Hom complex.  The same canonical setup supplies the Koszul symmetric structure,
two-variable functoriality, and the degree-zero cocycle description of cochain maps.

@stack 0GWQ
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory
open CochainComplex.HomComplex
open CategoryTheory.CochainComplex.InternalHom

variable {R : Type u} [CommRing R]
variable (K L : CochainComplex (ModuleCat R) ℤ)

/- Remark 15.72.2: the closed internal Hom of module cochain complexes is naturally the
module-valued Hom-complex bifunctor. -/
@[stacks 0GWQ "closed symmetric module complexes and their internal Hom"]
#check moduleComplexNatIso (R := R)

#check @moduleCat
#check @CochainComplex.Koszul.symmetricCategory
#check Cocycle.equivHom K L
#check @CochainComplex.HomComplex.bifunctor

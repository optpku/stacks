/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.BaseChange.Derived.KFlat
public import ReasLib.Algebra.Homology.DifferentialGradedModule.BaseChange.Derived.Restriction.Ordinary
public import ReasLib.Algebra.Homology.DifferentialGradedModule.PropertyP.KFlat
import StacksCheckRecall

@[expose] public section

noncomputable section

open DifferentialGradedModule.BaseChange

/- Lemma 22.33.8 (0BYZ) (1): for a K-flat cochain DGA `A` over `R`, relative derived
tensoring along `A ⟶ A ⊗[R] S` is the total right derived functor of `M ↦ M ⊗[R] S`. -/
section RightDerived

universe uR uS uA

variable {R : Type uR} {S : Type uS} [CommRing R] [CommRing S] [Algebra R S]
variable (A : CochainDGAlgebra.{uR, uA} R) (hA : A.IsKFlat)

@[stacks 0BYZ "Lemma 22.33.8 (0BYZ) (1): relative tensor is right-derived base change"]
#check derivedRightIso (S := S) A hA

end RightDerived

/- Lemma 22.33.8 (0BYZ) (2): the ordinary restriction-of-scalars square for base change
commutes on derived categories. -/
section Square

universe u

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable (A : CochainDGAlgebra.{u, u} R)

@[stacks 0BYZ "Lemma 22.33.8 (0BYZ) (2): ordinary restriction square"]
#check ordinaryRestrictionSquareIso (S := S) A

/- The underlying DGA-level square is the more general reusable companion. -/
#check restrictionSquareIso (S := S) A

end Square

/- Lemma 22.33.8 (0BYZ) (3): if `A` and the underlying `R`-complex of `M` are K-flat,
the ordinary tensor product represents relative derived tensor. -/
section Representation

universe uR uS uA

variable {R : Type uR} {S : Type uS} [CommRing R] [CommRing S] [Algebra R S]
variable (A : CochainDGAlgebra.{uR, uA} R) (hA : A.IsKFlat)
variable (M : DifferentialGradedModule.{uR, max uA uS} A) (hM : M.IsKFlat)

@[stacks 0BYZ "Lemma 22.33.8 (0BYZ) (3): K-flat ordinary representative"]
#check representationComparison_isIso_of_isKFlat (S := S) A hA M hM

/- The isomorphism wrapper exposes the same comparison for downstream `.hom`/`.inv` use. -/
#check representationIso (S := S) A hA M hM

end Representation

end

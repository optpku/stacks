module

public import ReasLib.AlgebraicTopology.CosimplicialObject.Homotopy.Equiv.QuasiIso
import StacksCheckRecall

/-!
@stack 0FKK

# Source-facing bridge for Lemma 14.28.7

Preservation of cosimplicial homotopy equivalences by alternating and normalized cochains is
owned by the corresponding neutral ReasLib leaves.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicTopology

noncomputable section

universe u v

namespace CategoryTheory.CosimplicialObject

section Alternating

variable {A : Type u} [Category.{v} A] [Preadditive A] [HasFiniteBiproducts A]
variable {U V : CosimplicialObject A} {a : U ⟶ V}
variable (ha : IsHomotopyEquivalence a) (e : HomotopyEquiv U V)

/- Lemma 14.28.7 (1): alternating cochains preserve cosimplicial homotopy equivalences. The
canonical ReasLib predicate is product-free, and the next bridge identifies it with the source
cotensor criterion under the additive hypotheses. -/
@[stacks 0FKK "Lemma 14.28.7 (1)"]
#check (ha.alternatingCoface :
  HomologicalComplex.homotopyEquivalences A (ComplexShape.up ℕ)
    ((alternatingCofaceMapComplex A).map a))

/- The canonical owner also exposes preservation as an assumption-minimal inclusion of
morphism properties. -/
#check (homotopyEquivalences.alternatingCoface (A := A) :
  homotopyEquivalences A ≤
      (HomologicalComplex.homotopyEquivalences A (ComplexShape.up ℕ)).inverseImage
        (alternatingCofaceMapComplex A))

@[stacks 0FKK "Lemma 14.28.7: cotensor homotopy-equivalence criterion"]
#check (IsHomotopyEquivalence.cotensor.iff_exists_inverse a :
  IsHomotopyEquivalence a ↔
    ∃ g : V ⟶ U, Homotopic (a ≫ g) (𝟙 U) ∧ Homotopic (g ≫ a) (𝟙 V))

/- The structured companion retains the chosen product-free homotopy inverse. -/
#check (e.alternatingCoface :
  HomRel.Equiv (homotopic A (ComplexShape.up ℕ))
    ((alternatingCofaceMapComplex A).obj U) ((alternatingCofaceMapComplex A).obj V))

section QuasiIso

variable [CategoryWithHomology A]

/- Canonical quasi-isomorphism consequence at the weaker category-with-homology layer. -/
#check (homotopyEquivalences.alternatingCoface.le_quasiIso (A := A) :
  homotopyEquivalences A ≤
    (HomologicalComplex.quasiIso A (ComplexShape.up ℕ)).inverseImage
      (alternatingCofaceMapComplex A))

end QuasiIso

end Alternating

section Normalized

variable {A : Type u} [Category.{v} A] [Abelian A]
variable {U V : CosimplicialObject A} {a : U ⟶ V}
variable (ha : IsHomotopyEquivalence a) (e : HomotopyEquiv U V)

/- Lemma 14.28.7 (2): normalized cochains preserve cosimplicial homotopy equivalences. -/
@[stacks 0FKK "Lemma 14.28.7 (2)"]
#check (ha.normalizedCochain :
  HomologicalComplex.homotopyEquivalences A (ComplexShape.up ℕ)
    (normalizedCochainComplex.functor.map a))

/- The canonical owner also exposes preservation as an inclusion of morphism properties. -/
#check (homotopyEquivalences.normalizedCochain (A := A) :
  homotopyEquivalences A ≤
    (HomologicalComplex.homotopyEquivalences A (ComplexShape.up ℕ)).inverseImage
      normalizedCochainComplex.functor)

/- The structured companion retains the chosen product-free homotopy inverse. -/
#check (e.normalizedCochain :
  HomRel.Equiv (homotopic A (ComplexShape.up ℕ))
    (normalizedCochainComplex.functor.obj U) (normalizedCochainComplex.functor.obj V))

/- Canonical quasi-isomorphism consequence for normalized cochains. -/
#check (homotopyEquivalences.normalizedCochain.le_quasiIso (A := A) :
  homotopyEquivalences A ≤
    (HomologicalComplex.quasiIso A (ComplexShape.up ℕ)).inverseImage
      normalizedCochainComplex.functor)

end Normalized

section Canonical

variable {A : Type u} [Category.{v} A] [Abelian A]
variable {U V : CosimplicialObject A} (e : HomotopyEquiv U V)
variable {a : U ⟶ V}

/- Lemma 14.28.7: the canonical image quotient is the reusable normalized cochain target. -/
#check (homotopyEquivalences.degenerate.normalized (A := A) :
  homotopyEquivalences A ≤
    (HomologicalComplex.homotopyEquivalences A (ComplexShape.up ℕ)).inverseImage
      (DoldKan.degenerate.normalized.functor (A := A)))

/- The structured companion retains the chosen inverse on the canonical normalized image. -/
#check (HomotopyEquiv.degenerate.normalized e :
  HomRel.Equiv (homotopic A (ComplexShape.up ℕ))
    ((DoldKan.degenerate.normalized.functor (A := A)).obj U)
    ((DoldKan.degenerate.normalized.functor (A := A)).obj V))

/- Canonical normalized image homotopy equivalences are quasi-isomorphisms. -/
#check (homotopyEquivalences.degenerate.normalized.le_quasiIso (A := A) :
  homotopyEquivalences A ≤
    (HomologicalComplex.quasiIso A (ComplexShape.up ℕ)).inverseImage
      (DoldKan.degenerate.normalized.functor (A := A)))

/- The pointwise property form is available without constructing a structured witness. -/
#check (IsHomotopyEquivalence.degenerate.normalized (A := A) :
  IsHomotopyEquivalence a →
    HomologicalComplex.homotopyEquivalences A (ComplexShape.up ℕ)
      ((DoldKan.degenerate.normalized.functor (A := A)).map a))

end Canonical

end CategoryTheory.CosimplicialObject

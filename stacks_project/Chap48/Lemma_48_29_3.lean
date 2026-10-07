module

public import ReasLib.AlgebraicGeometry.Scheme.Compactification.UpperShriek.FundamentalClass
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Compactification.Of.UpperShriek
open AlgebraicGeometry.RingedSpace.ModuleDerived
open scoped AlgebraicGeometry

universe u

/- Lemma 48.29.3: if `Y` is Cohen–Macaulay, `f` admits an immersion followed by a
proper smooth factorization, is Koszul at points of local dimension at most one,
and has generic residue-field transcendence degree `r`, then the fundamental-class
map from `Λ[r] Ω` to the degree `−r` upper-shriek cohomology sheaf is an isomorphism
on smooth stalks. -/
@[stacks 0EA0] #check
  (AlgebraicGeometry.Scheme.Compactification.Of.UpperShriek.existsFundamentalClass_of_koszulAt_le_one :
    {S : Scheme.{u}} → [IsNoetherian S] →
      {X Y : FiniteTypeSeparatedOver S} → (f : X ⟶ Y) →
      [Scheme.CohenMacaulay Y.obj.left] →
      {P : Scheme.{u}} → (i : X.obj.left ⟶ P) → (g : P ⟶ Y.obj.left) →
      (factorization : i ≫ g = f.hom.left) → [IsImmersion i] → [IsProper g] →
      [Smooth g] → (Q : Compactification.Of Y.obj.left (Over.mk f.hom.left)) →
      (A : DerivedQCoh.PlusRightAdjoint (Compactification.Of.ambientMorphism Q)) →
      (r : ℕ) →
      (hKoszul : ∀ x : X.obj.left,
        ringKrullDim ((X.obj.left).presheaf.stalk x) ≤ 1 → KoszulAt f.hom.left x) →
      (htrdeg : ∀ ξ : X.obj.left,
        ξ ∈ genericPoints X.obj.left → residueFieldTrdegAt f.hom.left ξ = r) →
      ∃ φ : (Λ[r] Ω[LocallyRingedSpace.Hom.toShHom
          (Scheme.Hom.toLRSHom f.hom.left)]) ⟶
          cohomologySheaf (dualizingObject f Q A).obj (-(r : ℤ)),
        ∀ x : X.obj.left,
          SmoothAt f.hom.left x → IsIso (RingedSpace.moduleStalkHom x φ))

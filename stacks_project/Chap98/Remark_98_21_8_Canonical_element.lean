module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.CanonicalElement
public import ReasLib.AlgebraicGeometry.GroupoidsOver.CanonicalElement.Residue
import StacksCheckRecall

/-!
# Canonical element and the induced residue tangent map

The universal differential section defines the canonical lift. At a finite type
residue point, the object-induced tangent map evaluates residue derivations on
this element, followed by the residue tangent comparison.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor
open AlgebraicGeometry.GroupoidsOver

universe u

variable {S : Scheme.{u}} {X : GroupoidsOver S} [HasStrongRimSchlessinger X]
variable {Λ A : CommRingCat.{u}} (v : Λ ⟶ A)
variable {σΛ : Spec Λ ⟶ S} {σA : Spec A ⟶ S} (hv : Spec.map v ≫ σΛ = σA)
variable (x : X.p.Fiber (Over.mk σA)) (h_open : IsOpenImmersion σΛ)

/- Remark 98.21.8 (Canonical element)
The class of pullback along `a ↦ (a, d a)` is the canonical tangent element.
-/
@[stacks 07YC] #check (AlgebraicGeometry.GroupoidsOver.canonicalElement v hv x h_open :
  (tangentFunctor x).obj (CommRingCat.KaehlerDifferential v))

variable (u0 : Spec A) (π : A ⟶ (Spec A).residueField u0)
variable (hπ : Spec.map π = (Spec A).fromSpecResidueField u0)

#check (AlgebraicGeometry.GroupoidsOver.affineTangentVector_bijective v hv u0 π h_open hπ :
  Function.Bijective (affineTangentVector v hv (σA := σA) u0 π))

#check (AlgebraicGeometry.GroupoidsOver.residueTangentMap_bijective u0 π x :
  Function.Bijective (residueTangentMap u0 π x))

variable (h_noetherian : IsNoetherianRing Λ) (h_finiteType : v.hom.FiniteType)
variable (h_finiteTypePoint : IsFiniteTypePoint u0)
variable (θ : CommRingCat.KaehlerDifferential v ⟶ residueModule π)

#check (AlgebraicGeometry.GroupoidsOver.inducedTangentMap_apply v hv u0 π x h_open
  h_noetherian h_finiteType h_finiteTypePoint hπ θ :
  inducedTangentMap u0 π x (affineTangentVector v hv u0 π θ) =
    residueTangentMap u0 π x
      ((tangentFunctor x).map θ (canonicalElement v hv x h_open)))

/- The identification of linear maps from differentials with relative derivations
is the existing Kähler universal property. -/
section Derivations
variable (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]
variable {M : Type u} [AddCommGroup M] [Module R M] [Module B M]
variable [IsScalarTower R B M]

#check (_root_.KaehlerDifferential.linearMapEquivDerivation R B :
  (_root_.KaehlerDifferential R B →ₗ[B] M) ≃ₗ[B] _root_.Derivation R B M)

end Derivations

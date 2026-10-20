module

public import Mathlib.Algebra.Module.Equiv.Defs
public import stacks_project.Chap90.Lemma_90_19_7_TangentSpace

public import ReasLib.AlgebraicGeometry.FormalDeformation.InfinitesimalAutomorphisms.TangentComparison

/-!
# Canonical comparison of identity-tangent spaces

Typed compatibility checks for residue-pushforward comparisons and an explicit
strongly cocartesian factorization adapter.
-/

@[expose] public section

noncomputable section

open CategoryTheory hiding Linear
open CategoryTheory.Functor
open CategoryTheory.Functor.Fiber
open ArtinianLocalAlgCat

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{w} F]

namespace CategoryTheory.Functor

variable (p : F ⥤ ArtinianLocalAlgCat Λ k)

/-- Strongly cocartesian factorization of a lift, with the `IsHomLift` hypothesis
taken as an explicit parameter. -/
def homLiftMap {R S S' : ArtinianLocalAlgCat Λ k} {a b b' : F}
    (f : R ⟶ S) (φ : a ⟶ b) (hφ : p.IsStronglyCocartesian f φ)
    (g : S ⟶ S') (f' : R ⟶ S') (hf' : f' = f ≫ g) (φ' : a ⟶ b')
    (hφ' : p.IsHomLift f' φ') : b ⟶ b' :=
  @IsStronglyCocartesian.map _ _ _ _ p R S a b f φ hφ S' b' g f' hf' φ' hφ'

end CategoryTheory.Functor

#check (CategoryTheory.Functor.residuePushforward :
  ∀ (p : F ⥤ ArtinianLocalAlgCat Λ k) [p.op.IsFibered] (x : F),
    p.Fiber (residue Λ k))

#check (CategoryTheory.Functor.idTangentSpaceObjIso :
  ∀ (p : F ⥤ ArtinianLocalAlgCat Λ k) [p.op.IsFibered] (x : F),
    idTangentSpaceObj p x ≅ idTangentSpaceObj p (residuePushforwardObj p x))

#check (CategoryTheory.Functor.idTangentSpaceMulEquiv :
  ∀ (p : F ⥤ ArtinianLocalAlgCat Λ k) [Functor.IsFibered.InGroupoids p.op] (x : F),
    idTangentSpace p x ≃* idTangentSpace p (residuePushforwardObj p x))

#check (CategoryTheory.Functor.idTangentSpaceLinearEquiv :
  ∀ (p : F ⥤ ArtinianLocalAlgCat Λ k) [HasRimSchlessinger p] (x : F),
    idTangentSpace p x ≃ₗ[k] idTangentSpace p (residuePushforwardObj p x))

#check (CategoryTheory.Functor.idTangentSpaceLinearEquivOfPushforward :
  ∀ (p : F ⥤ ArtinianLocalAlgCat Λ k) [HasRimSchlessinger p]
    (x : F) (x0 : p.Fiber (residue Λ k)) (φ : x ⟶ fiberInclusion.obj x0)
    [p.IsStronglyCocartesian (toResidue (p.obj x)) φ],
    idTangentSpace p x ≃ₗ[k] idTangentSpace p (fiberInclusion.obj x0))

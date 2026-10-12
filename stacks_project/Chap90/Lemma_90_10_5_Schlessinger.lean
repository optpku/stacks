/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.Schlessinger.Automorphisms

/-!
# Automorphism pushforward along `k[ε] ⟶ k`

Given a morphism of a category cofibered in groupoids over `ArtinianLocalAlgCat Λ k`
lying over `k[ε] ⟶ k`, cartesian fill-in of `φ.op` induces a pushforward map on fibre
automorphisms.
-/

@[expose] public section

open CategoryTheory IsHomLift ArtinianLocalAlgCat

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{w} F]

namespace CategoryTheory.Functor

#check (CategoryTheory.Functor.isHomLift_op_comp_fiberHom :
  ∀ {p : F ⥤ ArtinianLocalAlgCat Λ k} {xε x0 : F}
      (φ : xε ⟶ x0) [p.IsHomLift (dualNumberToResidue Λ k) φ]
      (α : xε ⟶ xε) [p.IsHomLift (𝟙 (dualNumber Λ k)) α],
    p.op.IsHomLift (p.op.map φ.op) (φ.op ≫ α.op))

#check (CategoryTheory.Functor.autPushforwardHom :
  ∀ (p : F ⥤ ArtinianLocalAlgCat Λ k) [IsFibered.InGroupoids p.op]
      {xε x0 : F} (φ : xε ⟶ x0) [p.IsHomLift (dualNumberToResidue Λ k) φ]
      (α : xε ⟶ xε) [p.IsHomLift (𝟙 (dualNumber Λ k)) α],
    x0 ⟶ x0)

#check (CategoryTheory.Functor.autPushforwardHom_isHomLift :
  ∀ (p : F ⥤ ArtinianLocalAlgCat Λ k) [IsFibered.InGroupoids p.op]
      {xε x0 : F} (φ : xε ⟶ x0) [p.IsHomLift (dualNumberToResidue Λ k) φ]
      (α : xε ⟶ xε) [p.IsHomLift (𝟙 (dualNumber Λ k)) α],
    p.IsHomLift (𝟙 (residue Λ k)) (autPushforwardHom p φ α))

#check (CategoryTheory.Functor.autPushforward :
  ∀ (p : F ⥤ ArtinianLocalAlgCat Λ k) [IsFibered.InGroupoids p.op]
      {xε x0 : F} (φ : xε ⟶ x0) [p.IsHomLift (dualNumberToResidue Λ k) φ]
      (α : Aut (Fiber.mk (domain_eq p (dualNumberToResidue Λ k) φ))),
    Aut (Fiber.mk (codomain_eq p (dualNumberToResidue Λ k) φ)))

#check (CategoryTheory.Functor.autPushforward_spec :
  ∀ (p : F ⥤ ArtinianLocalAlgCat Λ k) [IsFibered.InGroupoids p.op]
      {xε x0 : F} (φ : xε ⟶ x0) [p.IsHomLift (dualNumberToResidue Λ k) φ]
      (α : Aut (Fiber.mk (domain_eq p (dualNumberToResidue Λ k) φ))),
    φ ≫ Fiber.fiberInclusion.map (autPushforward p φ α).hom =
      Fiber.fiberInclusion.map α.hom ≫ φ)

end CategoryTheory.Functor

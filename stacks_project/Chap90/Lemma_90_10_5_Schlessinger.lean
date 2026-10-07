module

public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.CategoryTheory.FiberedCategory.Cartesian
public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import ReasLib.CategoryTheory.Fibered.InGroupoids.Basic
public import stacks_project.Chap90.Definition_90_10_1_Schlessinger

/-!
# Automorphism pushforward along `k[ε] ⟶ k`

Given a morphism of a category cofibered in groupoids over `ArtinianLocalAlgCat Λ k`
lying over `k[ε] ⟶ k`, cartesian fill-in of `φ.op` induces a pushforward map on fibre
automorphisms. Schlessinger's conditions (S1) and (S2) are imported from
`Definition_90_10_1_Schlessinger`.
-/

@[expose] public section

open CategoryTheory IsHomLift ArtinianLocalAlgCat

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{w} F]

namespace CategoryTheory.Functor

/-- A fibre endomorphism of `xε` remains a lift of `p.map φ` after opposite composition with
`φ.op`. -/
theorem isHomLift_op_comp_fiberHom {p : F ⥤ ArtinianLocalAlgCat Λ k} {xε x0 : F}
    (φ : xε ⟶ x0) [p.IsHomLift (dualNumberToResidue Λ k) φ]
    (α : xε ⟶ xε) [p.IsHomLift (𝟙 (dualNumber Λ k)) α] :
    p.op.IsHomLift (p.op.map φ.op) (φ.op ≫ α.op) := sorry

/-- The underlying endomorphism of `x0` obtained by cartesian fill-in of a fibre endomorphism of
`xε` along `φ.op`. -/
noncomputable def autPushforwardHom (p : F ⥤ ArtinianLocalAlgCat Λ k)
    [IsFibered.InGroupoids p.op] {xε x0 : F} (φ : xε ⟶ x0)
    [p.IsHomLift (dualNumberToResidue Λ k) φ]
    (α : xε ⟶ xε) [p.IsHomLift (𝟙 (dualNumber Λ k)) α] :
    x0 ⟶ x0 :=
  (@IsCartesian.map _ _ _ _ p.op _ _ _ _ (p.op.map φ.op) φ.op inferInstance _
      (φ.op ≫ α.op) (isHomLift_op_comp_fiberHom φ α)).unop

/-- The cartesian fill-in of a fibre endomorphism of `xε` along `φ` lifts the identity on `k`. -/
theorem autPushforwardHom_isHomLift (p : F ⥤ ArtinianLocalAlgCat Λ k)
    [IsFibered.InGroupoids p.op] {xε x0 : F} (φ : xε ⟶ x0)
    [p.IsHomLift (dualNumberToResidue Λ k) φ]
    (α : xε ⟶ xε) [p.IsHomLift (𝟙 (dualNumber Λ k)) α] :
    p.IsHomLift (𝟙 (residue Λ k)) (autPushforwardHom p φ α) := sorry

/-- Pushforward of fibre automorphisms along a morphism lying over `k[ε] ⟶ k`, obtained from the
cartesian fill-in of `φ.op`. -/
noncomputable def autPushforward (p : F ⥤ ArtinianLocalAlgCat Λ k)
    [hG : IsFibered.InGroupoids p.op] {xε x0 : F} (φ : xε ⟶ x0)
    [hφ : p.IsHomLift (dualNumberToResidue Λ k) φ]
    (α : Aut (Fiber.mk (domain_eq p (dualNumberToResidue Λ k) φ))) :
    Aut (Fiber.mk (codomain_eq p (dualNumberToResidue Λ k) φ)) :=
  Iso.mk
    ⟨@autPushforwardHom _ _ _ _ _ _ _ _ _ p hG _ _ φ hφ
        (Fiber.fiberInclusion.map α.hom) α.hom.property,
      @autPushforwardHom_isHomLift _ _ _ _ _ _ _ _ _ p hG _ _ φ hφ
        (Fiber.fiberInclusion.map α.hom) α.hom.property⟩
    ⟨@autPushforwardHom _ _ _ _ _ _ _ _ _ p hG _ _ φ hφ
        (Fiber.fiberInclusion.map α.inv) α.inv.property,
      @autPushforwardHom_isHomLift _ _ _ _ _ _ _ _ _ p hG _ _ φ hφ
        (Fiber.fiberInclusion.map α.inv) α.inv.property⟩
    sorry sorry

/-- Pushforward of a fibre automorphism `α` of `xε` along `φ` is characterised by
`φ ≫ β = α ≫ φ`. -/
theorem autPushforward_spec (p : F ⥤ ArtinianLocalAlgCat Λ k)
    [IsFibered.InGroupoids p.op] {xε x0 : F} (φ : xε ⟶ x0)
    [p.IsHomLift (dualNumberToResidue Λ k) φ]
    (α : Aut (Fiber.mk (domain_eq p (dualNumberToResidue Λ k) φ))) :
    φ ≫ Fiber.fiberInclusion.map (autPushforward p φ α).hom =
      Fiber.fiberInclusion.map α.hom ≫ φ := sorry

end CategoryTheory.Functor

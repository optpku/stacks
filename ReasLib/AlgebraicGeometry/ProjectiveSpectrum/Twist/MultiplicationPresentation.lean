/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Twist.Presentation
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Twist.Multiplication
public import ReasLib.AlgebraicGeometry.Scheme.Module.Pullback.Monoidal
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Sections.Tensor
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.TopSections

/-!
# Multiplication presentations for twists on projective spectra

A multiplication presentation records explicit morphisms between integral twists and identifies
their action on top sections after arbitrary pullback.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry TensorProduct

noncomputable section

universe u

namespace AlgebraicGeometry

variable {A : Type u} {σ : Type u}
variable [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- An explicit multiplication on the twists of a chosen projective-spectrum presentation,
together with its sectionwise compatibility with the presentation's graded multiplication. -/
structure ProjTwistMulPresentation (P : ProjTwistPresentation 𝒜) where
  /-- The multiplication morphisms from the tensor product of twists of degrees `a` and `b`
  to the twist of degree `a + b`. -/
  hom :
    ∀ a b : ℤ,
      (tensorObj (P.actualTwist a) (P.actualTwist b) : (Proj 𝒜).Modules) ⟶
        P.actualTwist (a + b)
  /-- On top sections after every scheme pullback, the multiplication morphisms agree with the
  graded multiplication carried by the twist presentation. -/
  top_hom_spec :
    ∀ {X : Scheme.{u}}
      [SheafOfModules.UnitIsSheafifiedUnit X.ringCatSheaf]
      (r : X ⟶ Proj 𝒜) (a b : ℤ),
      ∀ x : Γ(((Scheme.Modules.pullback r).obj (P.actualTwist a)), ⊤),
        ∀ y : Γ(((Scheme.Modules.pullback r).obj (P.actualTwist b)), ⊤),
            (SheafOfModules.sectionsMap
              (Scheme.Modules.pullbackTensorMap r (hom a b))
            (RingedSpace.tensorSection (X := X.toRingedSpace)
              (ℱ := ((Scheme.Modules.pullback r).obj (P.actualTwist a)))
              (𝒢 := ((Scheme.Modules.pullback r).obj (P.actualTwist b)))
                (RingedSpace.sectionFromTop
                  ((Scheme.Modules.pullback r).obj (P.actualTwist a)) x)
                (RingedSpace.sectionFromTop
                  ((Scheme.Modules.pullback r).obj (P.actualTwist b)) y))).1
            (Opposite.op (⊤ : X.Opens)) =
            P.actualMul r (Opposite.op (⊤ : X.Opens)) a b x y

namespace ProjTwistMulPresentation

/-- Construct a twist-multiplication presentation from an explicit multiplication family and
its top-sections compatibility law. -/
def ofHom (P : ProjTwistPresentation 𝒜)
    (hom :
      ∀ a b : ℤ,
        (tensorObj (P.actualTwist a) (P.actualTwist b) : (Proj 𝒜).Modules) ⟶
          P.actualTwist (a + b))
    (top_hom_spec :
      ∀ {X : Scheme.{u}}
        [SheafOfModules.UnitIsSheafifiedUnit X.ringCatSheaf]
        (r : X ⟶ Proj 𝒜) (a b : ℤ),
        ∀ x : Γ(((Scheme.Modules.pullback r).obj (P.actualTwist a)), ⊤),
          ∀ y : Γ(((Scheme.Modules.pullback r).obj (P.actualTwist b)), ⊤),
            (SheafOfModules.sectionsMap
                (Scheme.Modules.pullbackTensorMap r (hom a b))
              (RingedSpace.tensorSection (X := X.toRingedSpace)
                (ℱ := ((Scheme.Modules.pullback r).obj (P.actualTwist a)))
                (𝒢 := ((Scheme.Modules.pullback r).obj (P.actualTwist b)))
                  (RingedSpace.sectionFromTop
                    ((Scheme.Modules.pullback r).obj (P.actualTwist a)) x)
                  (RingedSpace.sectionFromTop
                    ((Scheme.Modules.pullback r).obj (P.actualTwist b)) y))).1
              (Opposite.op (⊤ : X.Opens)) =
              P.actualMul r (Opposite.op (⊤ : X.Opens)) a b x y) :
    ProjTwistMulPresentation 𝒜 P where
  hom := hom
  top_hom_spec := top_hom_spec

end ProjTwistMulPresentation

/-- The raw multiplication family underlying a multiplication presentation of projective
twists. -/
abbrev ProjTwistMulFamily (P : ProjTwistPresentation 𝒜) :=
  ∀ a b : ℤ,
    (tensorObj (P.actualTwist a) (P.actualTwist b) : (Proj 𝒜).Modules) ⟶
      P.actualTwist (a + b)

/-- A multiplication family is compatible with a twist presentation when it induces the
presentation's graded multiplication on top sections after every scheme pullback. -/
abbrev projTwistMulCompatibilityProp
    (P : ProjTwistPresentation 𝒜) (twistMul : ProjTwistMulFamily 𝒜 P) : Prop :=
  ∀ {X : Scheme.{u}}
      [SheafOfModules.UnitIsSheafifiedUnit X.ringCatSheaf]
      (r : X ⟶ Proj 𝒜) (a b : ℤ),
    ∀ x : Γ(((Scheme.Modules.pullback r).obj (P.actualTwist a)), ⊤),
      ∀ y : Γ(((Scheme.Modules.pullback r).obj (P.actualTwist b)), ⊤),
        (SheafOfModules.sectionsMap
            (Scheme.Modules.pullbackTensorMap r (twistMul a b))
            (RingedSpace.tensorSection (X := X.toRingedSpace)
              (ℱ := ((Scheme.Modules.pullback r).obj (P.actualTwist a)))
              (𝒢 := ((Scheme.Modules.pullback r).obj (P.actualTwist b)))
              (RingedSpace.sectionFromTop
                ((Scheme.Modules.pullback r).obj (P.actualTwist a)) x)
              (RingedSpace.sectionFromTop
                ((Scheme.Modules.pullback r).obj (P.actualTwist b)) y))).1
          (Opposite.op (⊤ : X.Opens)) =
          P.actualMul r (Opposite.op (⊤ : X.Opens)) a b x y

/-- The proposition view of the top-sections law carried by a multiplication presentation. -/
abbrev ProjTwistMulPresentation.topCompatibilityProp
    (P : ProjTwistPresentation 𝒜) (T : ProjTwistMulPresentation 𝒜 P) : Prop :=
  projTwistMulCompatibilityProp 𝒜 P T.hom

/-- A multiplication presentation satisfies its proposition-level top-sections compatibility
specification. -/
theorem ProjTwistMulPresentation.topCompatibilityProp_spec
    (P : ProjTwistPresentation 𝒜) (T : ProjTwistMulPresentation 𝒜 P) :
    T.topCompatibilityProp := T.top_hom_spec

/-- The action of a projective twist on a module already tensored with another twist. -/
abbrev projSheafTwistMulMap
    (P : ProjTwistPresentation 𝒜)
    (twistMul : ProjTwistMulFamily 𝒜 P)
    (ℱ : (Proj 𝒜).Modules) (a b : ℤ) :
    (tensorObj (P.actualTwist a) (P.tensorTwist ℱ b) : (Proj 𝒜).Modules) ⟶
      P.tensorTwist ℱ (a + b) :=
  projSheafTwistMul 𝒜 P.actualTwist twistMul ℱ a b

end AlgebraicGeometry

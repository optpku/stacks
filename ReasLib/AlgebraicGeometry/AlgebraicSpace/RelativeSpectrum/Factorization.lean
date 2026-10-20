/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeSpectrum.Universal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Algebra.Pushforward
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback

/-!
# Canonical factorization through the relative spectrum of a pushforward algebra

A quasi-compact quasi-separated morphism factors canonically through the relative
spectrum of its pushforward structure algebra. The first factor also defines a
section of the pullback of the structural projection.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- The canonical first-factor morphism `X ⟶ relativeSpec (f_* 𝒪_X)` of a
quasi-compact quasi-separated morphism. -/
def Hom.toPushforwardRelativeSpec {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] :
    X ⟶ relativeSpec (pushforwardStructureQcAlgebra f) :=
  relativeSpecHomOfAlgebra (pushforwardStructureQcAlgebra f) f (𝟙 _)

/-- The component of the canonical first factor at a scheme point has base point
obtained by composing with the original morphism. -/
theorem Hom.toPushforwardRelativeSpec_app_toX {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] (T : (Over S)ᵒᵖ)
    (x : X.functorOfPoints.obj T) :
    ((Hom.toPushforwardRelativeSpec f).app T x).1 =
      yonedaEquiv ((yonedaEquiv.symm x ≫ f : yoneda.obj T.unop ⟶ Y.functorOfPoints)) :=
  rfl

/-- The canonical first factor followed by the relative-spectrum projection is the
original morphism. -/
theorem Hom.toPushforwardRelativeSpec_comp_relativeSpecπ {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] :
    Hom.toPushforwardRelativeSpec f ≫
        relativeSpecπ (pushforwardStructureQcAlgebra f) =
      f :=
  relativeSpecHomOfAlgebra_toBase (pushforwardStructureQcAlgebra f) f (𝟙 _)

/-- The section `X ⟶ X ×_Y relativeSpec (f_* 𝒪_X)` over `X` determined by the
canonical first factor. -/
def Hom.toPushforwardRelativeSpecOver {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] :
    X ⟶ pullback f (relativeSpecπ (pushforwardStructureQcAlgebra f)) :=
  pullback.lift (𝟙 X) (Hom.toPushforwardRelativeSpec f)
    (by rw [Category.id_comp, Hom.toPushforwardRelativeSpec_comp_relativeSpecπ])

/-- The section determined by the canonical first factor projects to the identity
on its source. -/
theorem Hom.toPushforwardRelativeSpecOver_fst {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] :
    Hom.toPushforwardRelativeSpecOver f ≫
        pullback.fst f (relativeSpecπ (pushforwardStructureQcAlgebra f)) =
      𝟙 X :=
  pullback.lift_fst _ _ _

/-- The second projection of the canonical pullback section is the canonical first
factor through the relative spectrum. -/
theorem Hom.toPushforwardRelativeSpecOver_snd {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] :
    Hom.toPushforwardRelativeSpecOver f ≫
        pullback.snd f (relativeSpecπ (pushforwardStructureQcAlgebra f)) =
      Hom.toPushforwardRelativeSpec f :=
  pullback.lift_snd _ _ _

end AlgebraicGeometry.AlgebraicSpace

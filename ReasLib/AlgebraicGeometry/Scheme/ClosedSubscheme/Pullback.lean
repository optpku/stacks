/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.Structure
public import ReasLib.AlgebraicGeometry.Scheme.IdealSubobject.Pullback
import Mathlib.Tactic.CrossRefAttribute

/-!
# Pullbacks of closed subschemes
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)

/-- Under base change of a closed immersion, the kernel ideal of the second projection is the
pullback of the original kernel ideal. -/
@[stacks 01JU]
theorem ker_pullback_snd [IsClosedImmersion f] :
    (pullback.snd f g).ker = f.ker.comap g := sorry

/-- The kernel ideal subobject of a pulled-back closed immersion is the image of the pulled-back
kernel ideal map. -/
@[stacks 01JU "closed-immersion pullback ideal as an image"]
theorem kernelIdealSubobject_pullback_snd [IsClosedImmersion f] :
    (pullback.snd f g).kernelIdealSubobject =
      LocallyRingedSpace.IdealSubobject.pullback f.kernelIdealSubobject g.toLRSHom := sorry

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.Scheme.ClosedSubschemeStructure

open TopologicalSpace

/-- Pulling back the defining ideal pulls back its prescribed support. -/
@[simp, stacks 01JV "support of an inverse-image closed subscheme"]
theorem support_comap
    {X Y : Scheme.{u}} {Z : Closeds Y}
    (T : ClosedSubschemeStructure Z) (f : X ⟶ Y) :
    (T.ideal.comap f).support = Z.preimage f.continuous := sorry

/-- The inverse-image scheme structure on the inverse image of a closed subset. -/
@[stacks 01JV "inverse image of a closed-subscheme structure"]
noncomputable def comap
    {X Y : Scheme.{u}} {Z : Closeds Y}
    (T : ClosedSubschemeStructure Z) (f : X ⟶ Y) :
    ClosedSubschemeStructure (Z.preimage f.continuous) where
  ideal := T.ideal.comap f
  support_eq := T.support_comap f

/-- The defining ideal of the inverse-image structure is the pulled-back ideal. -/
@[simp, stacks 01JV "ideal of an inverse-image closed subscheme"]
theorem comap_ideal
    {X Y : Scheme.{u}} {Z : Closeds Y}
    (T : ClosedSubschemeStructure Z) (f : X ⟶ Y) :
    (T.comap f).ideal = T.ideal.comap f := sorry

/-- The inverse-image structure is canonically the scheme-theoretic pullback. -/
@[stacks 01JV "inverse image as a pullback"]
noncomputable abbrev comapIso
    {X Y : Scheme.{u}} {Z : Closeds Y}
    (T : ClosedSubschemeStructure Z) (f : X ⟶ Y) :
    (T.comap f).subscheme ≅ pullback f T.ι :=
  T.ideal.comapIso f

/-- The pullback comparison followed by the first projection is the inverse-image closed
immersion. -/
@[reassoc (attr := simp), stacks 01JV "inverse-image comparison first projection"]
theorem comapIso_hom_fst
    {X Y : Scheme.{u}} {Z : Closeds Y}
    (T : ClosedSubschemeStructure Z) (f : X ⟶ Y) :
    (T.comapIso f).hom ≫ pullback.fst f T.ι = (T.comap f).ι := sorry

/-- The inverse pullback comparison followed by the inverse-image immersion is the first
projection from the scheme-theoretic pullback. -/
@[reassoc (attr := simp), stacks 01JV "inverse-image comparison inclusion"]
theorem comapIso_inv_ι
    {X Y : Scheme.{u}} {Z : Closeds Y}
    (T : ClosedSubschemeStructure Z) (f : X ⟶ Y) :
    (T.comapIso f).inv ≫ (T.comap f).ι = pullback.fst f T.ι := sorry

end AlgebraicGeometry.Scheme.ClosedSubschemeStructure

/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.ChosenCleavage.Pseudofunctor
public import ReasLib.CategoryTheory.Sites.Descent.HomPresheaf.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Local Hom presheaves of a fibred category

For a fibred projection `p : S ⥤ C`, an object `x` over `U`, an object `y` over `V`, and a
base arrow `f : U ⟶ V`, this module packages the presheaf of local morphisms
`x|_T ⟶ (f⁎ y)|_T` on `Over U`.  The underlying canonical construction is
`Pseudofunctor.presheafHom`; this file is the projection-level interface that keeps the target
reindexing attached to the base arrow.

The chosen-cleavage specialization is deliberate: `Functor.fiberPseudofunctor` is the existing
application-level owner for a merely fibred projection.  Consumers which already carry a
specific cleavage can use `Pseudofunctor.presheafHom` directly.
-/

@[expose] public section

universe u v uS vS

namespace CategoryTheory

open Opposite
open scoped CategoryTheory.Bicategory

namespace Functor

variable {C : Type u} [Category.{v} C]
variable {S : Type uS} [Category.{vS} S]

namespace LocalHom.Presheaf

/-- The presheaf of local morphisms from `x` to the reindexing of `y` along `f`.

At `g : W ⟶ U`, its sections are morphisms from `g⁎ x` to `(g ≫ f)⁎ y`, with the
    pseudofunctorial comparison built into the canonical Hom-presheaf restriction maps. -/
@[stacks 026A "fibered-projection Hom-presheaf specialization"]
noncomputable abbrev apply
    (p : S ⥤ C) [p.IsFibered] {U V : C}
    (x : p.Fiber U) (f : U ⟶ V) (y : p.Fiber V) :
    (Over U)ᵒᵖ ⥤ Type vS :=
    (fiberPseudofunctor p).presheafHom x
    (((fiberPseudofunctor p).map f.op.toLoc).toFunctor.obj y)

namespace Identity

/-- The identity-slice readout of `LocalHom.Presheaf.apply` is the Hom-set from `x` to the chosen
reindexing of `y` along `f`. -/
noncomputable abbrev equiv
    (p : S ⥤ C) [p.IsFibered] {U V : C}
    (x : p.Fiber U) (f : U ⟶ V) (y : p.Fiber V) :
    (x ⟶ ((fiberPseudofunctor p).map f.op.toLoc).toFunctor.obj y) ≃
      (LocalHom.Presheaf.apply p x f y).obj (op (Over.mk (𝟙 U))) :=
  (fiberPseudofunctor p).presheafHomObjHomEquiv

end Identity

namespace ULift

/-- The universe-raised local Hom presheaf.  This is the canonical `ULift` transport used when
the plus construction is formed in the universe required by the slice site. -/
noncomputable abbrev apply
    (p : S ⥤ C) [p.IsFibered] {U V : C}
    (x : p.Fiber U) (f : U ⟶ V) (y : p.Fiber V) :
    (Over U)ᵒᵖ ⥤ Type (max vS (max u v)) :=
  LocalHom.Presheaf.apply p x f y ⋙
    (CategoryTheory.uliftFunctor.{max u v, vS} : Type vS ⥤ Type (max vS (max u v)))

namespace Restriction

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Restricting a lifted local Hom section and removing `ULift` is the normalized `pullHom`
restriction in the selected fiber pseudofunctor. -/
theorem down
    (p : S ⥤ C) [p.IsFibered] {U V : C}
    (x : p.Fiber U) (f : U ⟶ V) (y : p.Fiber V)
    {Y₀ Y₁ : Over U} (k : Y₁ ⟶ Y₀)
    (φ : (LocalHom.Presheaf.apply p x f y).obj (op Y₀)) :
    ((LocalHom.Presheaf.ULift.apply p x f y).map k.op (ULift.up φ)).down =
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (F := fiberPseudofunctor p) φ k.left Y₁.hom Y₁.hom k.w k.w := sorry

end Restriction

end ULift

end LocalHom.Presheaf

end Functor

end CategoryTheory

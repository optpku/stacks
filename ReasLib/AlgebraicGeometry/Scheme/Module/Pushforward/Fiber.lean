/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Topology.Sheaves.Stalks

/-!
# Restriction from pushforward stalks to fibre sections

The pullback adjunction unit restricts sections over a neighbourhood of a base
point to the scheme-theoretic fibre. Compatibility with restriction induces a
canonical map from the pushforward stalk to global sections on the fibre.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- Restriction of module sections over the preimage of a neighbourhood of a
base point to global sections of the pulled-back module on its fibre. -/
def sectionsToFiber {X Y : Scheme.{u}} (f : X ⟶ Y) (F : X.Modules)
    (y : Y) (U : Y.Opens) (hy : y ∈ U) :
    Γ(F, f ⁻¹ᵁ U) ⟶ Γ((Scheme.Modules.pullback (f.fiberι y)).obj F, ⊤) :=
  let inclusion : (⊤ : (f.fiber y).Opens) ⟶ (f.fiberι y) ⁻¹ᵁ (f ⁻¹ᵁ U) :=
    homOfLE (fun point _ =>
      Eq.mpr (congrArg (fun basePoint : Y => basePoint ∈ U)
        (Set.mem_singleton_iff.mp ((f.range_fiberι y).subset ⟨point, rfl⟩))) hy)
  Scheme.Modules.Hom.app
      ((Scheme.Modules.pullbackPushforwardAdjunction (f.fiberι y)).unit.app F) (f ⁻¹ᵁ U) ≫
    ((Scheme.Modules.pullback (f.fiberι y)).obj F).presheaf.map inclusion.op

/-- Restriction to fibre sections is compatible with shrinking the open
neighbourhood of the base point. -/
theorem sectionsToFiber_restrict {X Y : Scheme.{u}} (f : X ⟶ Y) (F : X.Modules)
    (y : Y) {U V : Y.Opens} (inclusion : U ⟶ V) (hy : y ∈ U) :
    F.presheaf.map ((Opens.map f.base).map inclusion).op ≫ sectionsToFiber f F y U hy =
      sectionsToFiber f F y V (inclusion.le hy) := sorry

/-- The canonical map from a pushforward stalk to global sections of the module
pulled back to the scheme-theoretic fibre. -/
def stalkToFiberSections {X Y : Scheme.{u}} (f : X ⟶ Y) (F : X.Modules) (y : Y) :
    ((Scheme.Modules.pushforward f).obj F).presheaf.stalk y ⟶
      Γ((Scheme.Modules.pullback (f.fiberι y)).obj F, ⊤) :=
  colimit.desc
    ((OpenNhds.inclusion y).op ⋙ ((Scheme.Modules.pushforward f).obj F).presheaf)
    { pt := Γ((Scheme.Modules.pullback (f.fiberι y)).obj F, ⊤)
      ι :=
        { app := fun neighbourhood =>
            sectionsToFiber f F y neighbourhood.unop.val neighbourhood.unop.property
          naturality := fun _ neighbourhood inclusion =>
            (sectionsToFiber_restrict f F y ((OpenNhds.inclusion y).map inclusion.unop)
              neighbourhood.unop.property).trans (Category.comp_id _).symm } }

/-- The stalk-to-fibre map sends the germ of a section to its canonical
restriction to the fibre. -/
theorem stalkToFiberSections_germ {X Y : Scheme.{u}} (f : X ⟶ Y) (F : X.Modules)
    (y : Y) (U : Y.Opens) (hy : y ∈ U) :
    ((Scheme.Modules.pushforward f).obj F).presheaf.germ U y hy ≫
      stalkToFiberSections f F y = sectionsToFiber f F y U hy := sorry

end AlgebraicGeometry.Scheme.Hom

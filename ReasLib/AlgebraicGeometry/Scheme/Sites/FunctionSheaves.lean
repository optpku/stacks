module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Extension.Standard.Sheaf
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Standard.Small
public import ReasLib.Algebra.Category.Ring.Sheaf.Units

/-!
# Global functions and units on scheme sites

Global sections define commutative-ring-valued presheaves on scheme-valued sites.
On the standard big sites and the small Zariski and étale sites these are sheaves,
and their objectwise units form commutative-group-valued sheaves.
-/

@[expose] public section

open CategoryTheory Opposite

noncomputable section

universe u v w

namespace AlgebraicGeometry.Scheme.Site

variable {C : Type w} [Category.{v} C]

/-- The commutative-ring presheaf of global sections of a scheme-valued functor. -/
abbrev commStructurePresheaf (F : C ⥤ Scheme.{u}) : Cᵒᵖ ⥤ CommRingCat.{u} :=
  F.op ⋙ Scheme.Γ

/-- The section ring at an object is the global-sections ring of its scheme. -/
theorem commStructurePresheaf_obj (F : C ⥤ Scheme.{u}) (U : C) :
    (commStructurePresheaf F).obj (op U) = CommRingCat.of Γ(F.obj U, ⊤) := sorry

/-- Restriction of global sections is pullback along the corresponding scheme morphism. -/
theorem commStructurePresheaf_map (F : C ⥤ Scheme.{u}) {U V : C} (g : U ⟶ V) :
    (commStructurePresheaf F).map g.op = (F.map g).appTop := sorry

end AlgebraicGeometry.Scheme.Site

namespace AlgebraicGeometry.StandardTopology.Big

/-- Global sections satisfy the sheaf condition on every standard big scheme site. -/
theorem commStructurePresheaf_isSheaf (τ : StandardTopology) (S : Scheme.{u}) :
    Presheaf.IsSheaf (τ.overTopology S)
      (Scheme.Site.commStructurePresheaf (Over.forget S)) := sorry

/-- The commutative-ring-valued sheaf of global functions on a standard big scheme site. -/
noncomputable def commStructureSheaf (τ : StandardTopology) (S : Scheme.{u}) :
    Sheaf (τ.overTopology S) CommRingCat.{u} :=
  ⟨Scheme.Site.commStructurePresheaf (Over.forget S),
    commStructurePresheaf_isSheaf τ S⟩

/-- The commutative-group-valued sheaf of invertible functions on a standard big scheme site. -/
noncomputable def unitsSheaf (τ : StandardTopology) (S : Scheme.{u}) :
    Sheaf (τ.overTopology S) CommGrpCat.{u} :=
  CategoryTheory.Sheaf.unitsSheaf (commStructureSheaf τ S)

end AlgebraicGeometry.StandardTopology.Big

namespace AlgebraicGeometry.SmallStandardTopology

/-- Global sections satisfy the sheaf condition on the small Zariski and étale sites. -/
theorem commStructurePresheaf_isSheaf (σ : SmallStandardTopology) (S : Scheme.{u}) :
    Presheaf.IsSheaf (σ.topology S)
      (Scheme.Site.commStructurePresheaf (σ.toScheme S)) := sorry

/-- The commutative-ring-valued sheaf of global functions on a standard small scheme site. -/
noncomputable def commStructureSheaf (σ : SmallStandardTopology) (S : Scheme.{u}) :
    Sheaf (σ.topology S) CommRingCat.{u} :=
  ⟨Scheme.Site.commStructurePresheaf (σ.toScheme S),
    commStructurePresheaf_isSheaf σ S⟩

/-- The commutative-group-valued sheaf of invertible functions on a standard small scheme site. -/
noncomputable def unitsSheaf (σ : SmallStandardTopology) (S : Scheme.{u}) :
    Sheaf (σ.topology S) CommGrpCat.{u} :=
  CategoryTheory.Sheaf.unitsSheaf (commStructureSheaf σ S)

end AlgebraicGeometry.SmallStandardTopology

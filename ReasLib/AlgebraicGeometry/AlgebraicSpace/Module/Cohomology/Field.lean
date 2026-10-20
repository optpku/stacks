module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Modules
public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections
public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.Algebra.Module.End
public import Mathlib.Algebra.Module.MinimalAxioms
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.SmallEtale.Modules

variable {k : Type u} [Field k] {X : AlgebraicSpace (Spec (CommRingCat.of k))}

/-- The underlying additive sheaf of a small étale module, lifted to a universe admitting
sheafification on the chart category. -/
def liftedAdditiveSheaf (F : Modules X) : Sheaf (topology X) AddCommGrpCat.{u + 1} :=
  (sheafCompose (topology X) AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
    ((SheafOfModules.toSheaf (structureSheaf X)).obj F)

/-- Small étale cohomology of a module is the cohomology of its underlying additive sheaf. -/
abbrev cohomology (F : Modules X) (degree : ℕ) : Type (u + 2) :=
  @Sheaf.H (site X) inferInstance (topology X) (liftedAdditiveSheaf F)
    inferInstance (HasExt.standard _) degree

/-- Multiplication by a base-field scalar commutes with the restriction maps of the
underlying additive presheaf. -/
private theorem scalarEndomorphism_naturality (F : Modules X) (scalar : k)
    {source target : (site X)ᵒᵖ} (map : source ⟶ target) :
    F.val.presheaf.map map ≫
        AddCommGrpCat.ofHom
          (Module.toAddMonoidEnd ((structureSheaf X).obj.obj target) (F.val.obj target)
            (Scheme.Hom.globalSectionsMap target.unop.left.hom scalar)) =
      AddCommGrpCat.ofHom
          (Module.toAddMonoidEnd ((structureSheaf X).obj.obj source) (F.val.obj source)
            (Scheme.Hom.globalSectionsMap source.unop.left.hom scalar)) ≫
        F.val.presheaf.map map := sorry

/-- A scalar of the base field acts on the additive sheaf through its image in the global
sections ring of each étale scheme chart. -/
@[no_expose] def scalarEndomorphism (F : Modules X) (scalar : k) :
    (SheafOfModules.toSheaf (structureSheaf X)).obj F ⟶
      (SheafOfModules.toSheaf (structureSheaf X)).obj F where
  hom :=
    { app := fun chart => AddCommGrpCat.ofHom
        (Module.toAddMonoidEnd ((structureSheaf X).obj.obj chart) (F.val.obj chart)
          (Scheme.Hom.globalSectionsMap chart.unop.left.hom scalar))
      naturality := fun _ _ map => scalarEndomorphism_naturality F scalar map }

/-- Scalar multiplication on small étale cohomology is induced by the scalar endomorphism
of the underlying additive sheaf. -/
instance cohomologySMul (F : Modules X) (degree : ℕ) : SMul k (cohomology F degree) where
  smul scalar value :=
    @Sheaf.H.map.{u + 2, u + 1} (site X) inferInstance (topology X)
      inferInstance (HasExt.standard _) (liftedAdditiveSheaf F) (liftedAdditiveSheaf F)
      ((sheafCompose (topology X) AddCommGrpCat.uliftFunctor.{u + 1, u}).map
        (scalarEndomorphism F scalar)) degree value

/-- Base-field scalar multiplication distributes over addition in small étale cohomology. -/
theorem cohomology_smul_add (F : Modules X) (degree : ℕ) (scalar : k)
    (left right : cohomology F degree) :
    scalar • (left + right) = scalar • left + scalar • right := sorry

/-- Addition of base-field scalars distributes over their action on small étale cohomology. -/
theorem cohomology_add_smul (F : Modules X) (degree : ℕ) (left right : k)
    (value : cohomology F degree) :
    (left + right) • value = left • value + right • value := sorry

/-- The product of two base-field scalars acts by their successive actions on cohomology. -/
theorem cohomology_mul_smul (F : Modules X) (degree : ℕ) (left right : k)
    (value : cohomology F degree) :
    (left * right) • value = left • (right • value) := sorry

/-- The unit scalar acts as the identity on small étale cohomology. -/
theorem cohomology_one_smul (F : Modules X) (degree : ℕ) (value : cohomology F degree) :
    (1 : k) • value = value := sorry

/-- Small étale cohomology is a module over the base field through its canonical scalar action. -/
instance cohomologyModule (F : Modules X) (degree : ℕ) : Module k (cohomology F degree) :=
  Module.ofMinimalAxioms (cohomology_smul_add F degree) (cohomology_add_smul F degree)
    (cohomology_mul_smul F degree) (cohomology_one_smul F degree)

end AlgebraicGeometry.AlgebraicSpace.SmallEtale.Modules

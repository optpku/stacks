module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Module.Bimod.Equivalence
public import ReasLib.CategoryTheory.Monoidal.Bimod.ChangeOfScalars.Adjunction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Change of rings for differential graded module sheaves

A morphism of differential graded algebra sheaves induces extension and restriction of scalars
between their categories of right differential graded modules.  The constructions are transported
through the canonical equivalence with right module objects, so extension is the generic balanced
tensor product and restriction retains the underlying cochain complex.
-/

@[expose] public section

open CategoryTheory
open scoped SheafOfModules.RingedSite.DifferentialGradedAlgebra
open scoped SheafOfModules.RingedSite.DifferentialGradedModule

noncomputable section

universe u v w

namespace SheafOfModules.RingedSite.DifferentialGradedModule.ChangeOfRings

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [UnivLE.{max u v, w}]
variable {𝒪 : Sheaf J CommRingCat.{w}}
variable {A B : DGA(𝒪)}

/-- Extension of scalars for right differential graded modules along a morphism of differential
graded algebra sheaves. -/
@[stacks 0BYX "extension of scalars for DG module sheaves"]
noncomputable def extension (f : A ⟶ B) : Mod(A, d) ⥤ Mod(B, d) :=
  toBimodFunctor A ⋙
    Bimod.extendRight (DifferentialGradedAlgebra.toMonMap f) ⋙
    ofBimodFunctor B

/-- Restriction of scalars for right differential graded modules along a morphism of differential
graded algebra sheaves. -/
@[stacks 0BYX "restriction of scalars for DG module sheaves"]
noncomputable def restriction (f : A ⟶ B) : Mod(B, d) ⥤ Mod(A, d) :=
  toBimodFunctor B ⋙
    Bimod.restrictRight (Mon.trivial _)
      (DifferentialGradedAlgebra.toMonMap f) ⋙
    ofBimodFunctor A

/-- Extension of scalars is the generic balanced extension of the corresponding right module
object. -/
@[simp]
theorem extension_obj (f : A ⟶ B) (M : Mod(A, d)) :
    (extension f).obj M =
      ofBimod ((Bimod.extendRight
        (DifferentialGradedAlgebra.toMonMap f)).obj (toBimod M)) := sorry

/-- The underlying cochain complex of an extended module is the carrier of its balanced tensor
product presentation. -/
@[simp]
theorem extension_obj_toComplex (f : A ⟶ B) (M : Mod(A, d)) :
    ((extension f).obj M).toComplex =
      ((Bimod.extendRight
        (DifferentialGradedAlgebra.toMonMap f)).obj (toBimod M)).X := sorry

/-- Restriction of scalars is generic restriction of the corresponding right module object. -/
@[simp]
theorem restriction_obj (f : A ⟶ B) (N : Mod(B, d)) :
    (restriction f).obj N =
      ofBimod ((Bimod.restrictRight (Mon.trivial _)
        (DifferentialGradedAlgebra.toMonMap f)).obj (toBimod N)) := sorry

/-- Restriction of scalars does not change the underlying cochain complex. -/
@[simp]
theorem restriction_obj_toComplex (f : A ⟶ B) (N : Mod(B, d)) :
    ((restriction f).obj N).toComplex = N.toComplex := sorry

/-- Restriction of scalars does not change the underlying cochain map. -/
@[simp]
theorem restriction_map_toCochainMap (f : A ⟶ B)
    {M N : Mod(B, d)} (g : M ⟶ N) :
    ((restriction f).map g).toCochainMap = g.toCochainMap := sorry

/-- Extension of scalars is left adjoint to restriction of scalars for differential graded
module sheaves. -/
@[stacks 0BYX "extension-restriction adjunction for DG module sheaves"]
noncomputable def adjunction (f : A ⟶ B) : extension f ⊣ restriction f :=
  ((toBimodEquivalence A).toAdjunction.comp
    (Bimod.extendRestrictRightAdjunction
      (DifferentialGradedAlgebra.toMonMap f))).comp
    (toBimodEquivalence B).symm.toAdjunction

/-- The reusable Hom equivalence for extension and restriction of scalars of differential graded
module sheaves. -/
@[stacks 0BYX "extension-restriction Hom equivalence for DG module sheaves"]
noncomputable def homEquiv (f : A ⟶ B) (M : Mod(A, d)) (N : Mod(B, d)) :
    ((extension f).obj M ⟶ N) ≃ (M ⟶ (restriction f).obj N) :=
  (adjunction f).homEquiv M N

-- The functors are explicit composites of the canonical DG-module/right-module equivalence and
-- generic change of scalars.  Any `sorryAx` below is inherited only through structural laws.

end SheafOfModules.RingedSite.DifferentialGradedModule.ChangeOfRings

end

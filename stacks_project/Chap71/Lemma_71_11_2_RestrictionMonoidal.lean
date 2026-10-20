module

public import stacks_project.Chap71.Lemma_71_11_2_RestrictionAdjunction
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.TensorPower

/-!
# Tensor comparison for extension from a represented scheme

The comparison maps are the adjunction mates of the sectionwise lax maps of
restriction. They are the usual strong monoidal maps of module inverse image.
Only invertibility and coherence are proof obligations; the maps are specified.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace AlgebraicGeometry.AlgebraicSpace.RelativeProj

noncomputable section
universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules.RestrictToScheme

variable {S : Scheme.{u}} (Z : Over S)

/-- The oplax structure consists of the actual adjunction mates of restriction. -/
instance extensionOplaxMonoidal : (extension Z).OplaxMonoidal :=
  (extensionAdjunction Z).leftAdjointOplaxMonoidal

/-- The unit mate is invertible for geometric module inverse image. -/
instance extensionUnit_isIso : IsIso (Functor.OplaxMonoidal.η (extension Z)) := sorry

/-- The tensor mate is invertible for geometric module inverse image. -/
instance extensionTensor_isIso (M N : Z.left.Modules) :
    IsIso (Functor.OplaxMonoidal.δ (extension Z) M N) := sorry

/-- The strong structure inverts the specified mates, not an arbitrary comparison. -/
instance extensionMonoidal : (extension Z).Monoidal :=
  Functor.Monoidal.ofOplaxMonoidal (extension Z)

/-- Extension of a tensor power, using the actual unit and tensor comparisons. -/
def extensionTensorPowerIso (L : Z.left.Modules) (n : ℕ) :
    (extension Z).obj (RingedSpace.TensorPower.sheaf L n) ≅
      tensorPowerUnit ((extension Z).obj L) n :=
  (extension Z).mapIso (RingedSpace.TensorPower.monoidalComparison.iso L n).symm ≪≫
    (Functor.Monoidal.tensorPowerIso (extension Z) L n).symm ≪≫
      tensorPowerWithDegreeZeroMapIso
        (Modules.structureModuleIsoTensorUnit (ofOver Z)).symm (Iso.refl _) n

end AlgebraicGeometry.AlgebraicSpace.Modules.RestrictToScheme

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.IsoComma
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Cover.Fppf
public import Mathlib.CategoryTheory.Sites.LocallySurjective

/-!
# Local surjectivity of the iso-comma structure map

The structure map `U ×_{f, U', t'} R' ⟶ U'` is locally surjective for the fppf
topology when it is an fppf covering, when the object map is locally surjective,
or when the object map is an fppf covering.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace.Hom

/-- If the iso-comma structure map `U ×_{f, U', t'} R' ⟶ U'` is an fppf
covering, then it is locally surjective for the fppf topology. -/
theorem isoCommaToTargetObject_isLocallySurjective_of_fppfCovering
    {S : Scheme.{u}} {B : AlgebraicSpace S} {G H : GroupoidAlgebraicSpace B}
    (f : Hom G H)
    [FppfCovering (fun _ : PUnit ↦ (isoComma f).U.left)
      (fun _ ↦ (isoCommaToTargetObject f).left)] :
    Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S)
      (isoCommaToTargetObject f).left := sorry

/-- If the object map of a morphism of groupoids is locally surjective for the
fppf topology, then its iso-comma structure map is locally surjective. -/
theorem isoCommaToTargetObject_isLocallySurjective_of_obj {S : Scheme.{u}}
    {B : AlgebraicSpace S} {G H : GroupoidAlgebraicSpace B} (f : Hom G H)
    (h_obj : Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) f.obj.left) :
    Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S)
      (isoCommaToTargetObject f).left := sorry

/-- If the object map of a morphism of groupoids is an fppf covering, then its
iso-comma structure map is locally surjective for the fppf topology. -/
theorem isoCommaToTargetObject_isLocallySurjective_of_obj_fppfCovering
    {S : Scheme.{u}} {B : AlgebraicSpace S} {G H : GroupoidAlgebraicSpace B}
    (f : Hom G H)
    [FppfCovering (fun _ : PUnit ↦ G.U.left) (fun _ ↦ f.obj.left)] :
    Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S)
      (isoCommaToTargetObject f).left := sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace.Hom

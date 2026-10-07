module

public import ReasLib.AlgebraicGeometry.Scheme.Germ
public import Mathlib.AlgebraicGeometry.Morphisms.Etale

@[expose] public section

namespace AlgebraicGeometry.Scheme.Germ.Hom

/-- A morphism of scheme germs is étale if it has an étale representative on an open
neighborhood of the distinguished source point. -/
def Etale {X Y : Germ} (f : Hom X Y) : Prop :=
  ∃ r : Representative X Y, mk r = f ∧ AlgebraicGeometry.Etale r.hom

/-- A morphism of scheme germs is étale exactly when it has an étale representative. -/
theorem etale_iff_exists_representation {X Y : Germ} (f : Hom X Y) :
    f.Etale ↔ ∃ r : Representative X Y, mk r = f ∧ AlgebraicGeometry.Etale r.hom := sorry

/-- A morphism of scheme germs is smooth if it has a smooth representative on an open
neighborhood of the distinguished source point. -/
def Smooth {X Y : Germ} (f : Hom X Y) : Prop :=
  ∃ r : Representative X Y, mk r = f ∧ AlgebraicGeometry.Smooth r.hom

/-- A morphism of scheme germs is smooth exactly when it has a smooth representative. -/
theorem smooth_iff_exists_representation {X Y : Germ} (f : Hom X Y) :
    f.Smooth ↔ ∃ r : Representative X Y, mk r = f ∧ AlgebraicGeometry.Smooth r.hom := sorry

end AlgebraicGeometry.Scheme.Germ.Hom

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat.Locus
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Modules

/- 37.16.2.1: The locus where `ℱ` is flat over both `Y` via `f` and `S` via `f ≫ g`. -/
@[stacks 05VI] #check
  (AlgebraicGeometry.Scheme.Modules.flatOverBothLocus :
    ∀ {S X Y : Scheme.{u}}, X.Modules → (X ⟶ Y) → (Y ⟶ S) → Set X)

/- Membership in the simultaneous flatness locus is flatness over both the intermediate scheme
and the base scheme. -/
#check
  (AlgebraicGeometry.Scheme.Modules.mem_flatOverBothLocus :
    ∀ {S X Y : Scheme.{u}} (ℱ : X.Modules) (f : X ⟶ Y) (g : Y ⟶ S) (x : X),
      x ∈ flatOverBothLocus ℱ f g ↔
        flatOverAt ℱ f x ∧ flatOverAt ℱ (f ≫ g) x)

/- The simultaneous flatness locus is the intersection of the two pointwise flatness loci. -/
#check
  (AlgebraicGeometry.Scheme.Modules.flatOverBothLocus_eq_inter :
    ∀ {S X Y : Scheme.{u}} (ℱ : X.Modules) (f : X ⟶ Y) (g : Y ⟶ S),
      flatOverBothLocus ℱ f g =
        {x : X | flatOverAt ℱ f x} ∩ {x : X | flatOverAt ℱ (f ≫ g) x})

end AlgebraicGeometry.Scheme.Modules

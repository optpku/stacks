module

public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedPoints.Relative.GenericFiber
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/- Lemma 37.25.2: if the associated points of the generic fiber of a finite-type
quasi-coherent finite-type module are not contained in an open subscheme, then the same
noncontainment holds on every fiber over some nonempty open subscheme of the irreducible base. -/
@[stacks 05KN] #check
  (AlgebraicGeometry.Scheme.Hom.exists_open_associatedPoints_fiber_not_subset :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [FiniteType f] [IrreducibleSpace Y]
      (ℱ : X.Modules) [ℱ.IsQuasicoherent] [ℱ.IsFiniteType] (U : X.Opens),
      ¬ (((Scheme.Modules.pullback (f.fiberι (genericPoint Y))).obj ℱ).associatedPoints ⊆
        (f.fiberι (genericPoint Y)) ⁻¹' (U : Set X)) →
      ∃ V : Y.Opens, Nonempty V ∧
        ∀ y : Y, y ∈ V →
          ¬ (((Scheme.Modules.pullback (f.fiberι y)).obj ℱ).associatedPoints ⊆
            (f.fiberι y) ⁻¹' (U : Set X)))

end AlgebraicGeometry.Scheme.Hom

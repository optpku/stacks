module

public import Mathlib.CategoryTheory.ObjectProperty.Retract
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Derived.Limits
public import ReasLib.Algebra.Homology.DifferentialGradedModule.PropertyP.Finite
public import ReasLib.CategoryTheory.Pretriangulated.CompactObject.Closure
import ReasLib.Algebra.Homology.DifferentialGradedModule.PropertyP.KProjective

/-!
# Finite-Cell Models of Compact Derived Objects

Finite-cell DG-modules define an object property in the intrinsic derived category through the
essential image of the module-to-derived functor.  This leaf owns finite-support factorization and
the identification of compact objects with the canonical retract closure of that property.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits DifferentialGradedCategory
open scoped DifferentialGradedCategory

namespace DifferentialGradedModule.Derived

open PropertyP

variable {R : Type u} [CommRing R]
variable (A : CochainDGAlgebra.{u, v} R)

/-- A map from a compact derived object into a property-P module factors through one filtration
stage.  This is the colimit-facing compactness primitive for finite-support arguments. -/
@[stacks 09R2 "compact factorization through a property-P stage"]
theorem exists_factorization_through_propertyP_stage
    (E : Category.{u, v} A) (hE : IsCompactObject E)
    {P : DifferentialGradedModule.{u, v} A} (F : Filtration A P)
    (f : E ⟶ (fromModules A).obj P) :
    ∃ (n : ℕ) (g : E ⟶ (fromModules A).obj (F.stage n)),
      g ≫ (fromModules A).map (F.coconeApp n) = f := sorry

/-- After mapping an arrow out of a compact object from a finite property-P stage to the ambient
module, it factors through a chosen finite-summand subfiltration. -/
@[stacks 09R2 "stagewise finite-subfiltration factorization"]
theorem exists_finiteSubfiltration_factorization_of_stage
    (E : Category.{u, v} A) (hE : IsCompactObject E)
    {P : DifferentialGradedModule.{u, v} A} (F : Filtration A P) (n : ℕ)
    (f : E ⟶ (fromModules A).obj (F.stage n)) :
    ∃ (F' : FiniteSubfiltration A F)
      (g : E ⟶ (fromModules A).obj F'.obj),
      g ≫ (fromModules A).map F'.subobject.arrow =
        f ≫ (fromModules A).map (F.coconeApp n) := sorry

/-- A map from a compact derived object into a module with a property-P filtration factors
through a DG-submodule retaining finitely many cell summands. -/
@[stacks 09R2 "finite-subfiltration factorization"]
theorem exists_finiteSubfiltration_factorization
    (E : Category.{u, v} A) (hE : IsCompactObject E)
    {P : DifferentialGradedModule.{u, v} A} (F : Filtration A P)
    (f : E ⟶ (fromModules A).obj P) :
    ∃ (F' : FiniteSubfiltration A F)
      (g : E ⟶ (fromModules A).obj F'.obj),
      g ≫ (fromModules A).map F'.subobject.arrow = f := sorry

/-- Lemma 22.36.3 (09R2): a map from a compact derived object into a DG-module with a chosen
finite property-P filtration factors through a DG-submodule retaining finitely many summands in
each filtration piece. -/
@[stacks 09R2]
theorem exists_factorization_through_finiteSubfiltration
    (E : Category.{u, v} A) (hE : IsCompactObject E)
    {P : DifferentialGradedModule.{u, v} A} (F : FiniteFiltration A P)
    (f : E ⟶ (fromModules A).obj P) :
    ∃ (F' : FiniteSubfiltration A F.toFiltration)
      (g : E ⟶ (fromModules A).obj F'.obj),
      g ≫ (fromModules A).map F'.subobject.arrow = f := sorry

/-- Derived objects represented by DG-modules with finite-cell property-P filtrations. -/
@[stacks 09R3 "finite-cell objects in the derived category"]
def finiteCell : ObjectProperty (Category.{u, v} A) :=
  (HasFiniteCellFiltration A).map (fromModules A)

/-- A derived object is finite-cell exactly when it is represented by a DG-module carrying a
finite-cell property-P filtration. -/
@[stacks 09R3 "finite-cell representation criterion"]
theorem finiteCell_iff (E : Category.{u, v} A) :
    finiteCell A E ↔
      ∃ (P : DifferentialGradedModule.{u, v} A), HasFiniteCellFiltration A P ∧
        Nonempty ((fromModules A).obj P ≅ E) := sorry

namespace FiniteCell

/-- Finite-cell derived objects are closed under isomorphisms. -/
@[stacks 09R3 "isomorphism stability of finite-cell objects"]
instance isClosedUnderIsomorphisms :
    (finiteCell A).IsClosedUnderIsomorphisms := sorry

/-- A finite-cell derived object is compact. -/
@[stacks 09R3 "finite-cell objects are compact"]
theorem isCompactObject {E : Category.{u, v} A} (hE : finiteCell A E) :
    IsCompactObject E := sorry

/-- Every object in the retract closure of finite-cell derived objects is compact. -/
@[stacks 09R3 "compactness of the finite-cell retract closure"]
theorem isCompactObject_of_mem_retractClosure {E : Category.{u, v} A}
    (hE : (finiteCell A).retractClosure E) : IsCompactObject E := sorry

/-- Every compact derived object belongs to the retract closure of finite-cell objects. -/
@[stacks 09R3 "compact objects lie in the finite-cell retract closure"]
theorem mem_retractClosure_of_isCompactObject {E : Category.{u, v} A}
    (hE : IsCompactObject E) : (finiteCell A).retractClosure E := sorry

/-- Proposition 22.36.4 (09R3): compact derived objects are exactly the retract closure of the
finite-cell objects. -/
@[stacks 09R3]
theorem isCompactObject_iff_mem_retractClosure (E : Category.{u, v} A) :
    IsCompactObject E ↔ (finiteCell A).retractClosure E := sorry

end FiniteCell

#synth (finiteCell A).IsClosedUnderIsomorphisms

end DifferentialGradedModule.Derived

module

public import ReasLib.CategoryTheory.Functor.Additive.FiniteProducts
public import ReasLib.Algebra.Category.ModuleCat.LinearLift
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits ZeroObject

universe u v

variable {R : Type u} [CommRing R]

section
variable (L : FGModuleCat.{v} R ⥤ ModuleCat.{v} R) [Functor.ModuleLinear R L]

/- Remark 90.11.3 (1): an R-linear functor L : FGModuleCat R ⥤ ModuleCat R
preserves finite products and sends the zero module to the zero module,
see Homology, Lemma 12.3.7. ModuleLinear extends Additive. -/
@[stacks 06I5] #check (CategoryTheory.Functor.preservesFiniteProducts_and_map_isZero L :
    PreservesFiniteProducts L ∧
      (∀ {M : FGModuleCat.{v} R}, IsZero M → IsZero (L.obj M)))
end

section
variable (L : FGModuleCat.{v} R ⥤ Type v) [PreservesFiniteProducts L] [Unique (L.obj 0)]

/- Remark 90.11.3 (3): a functor L : FGModuleCat R ⥤ Type that preserves finite
products and sends the zero module to a one-element set has a unique lift to an
R-linear functor, see Lemma 90.11.4. This is FGModuleCat.existsUnique_linearLift. -/
@[stacks 06I5] #check (FGModuleCat.existsUnique_linearLift L :
    ∃! F : FGModuleCat.{v} R ⥤ ModuleCat.{v} R,
      F.ModuleLinear R ∧ F ⋙ forget (ModuleCat.{v} R) = L)
end

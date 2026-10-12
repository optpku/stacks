/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import stacks_project.Chap90.Lemma_90_11_4
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits ZeroObject

universe u v

variable {R : Type u} [CommRing R]

section
variable (L : FGModuleCat.{v} R ⥤ ModuleCat.{v} R) [Functor.ModuleLinear R L]

/- Remark 90.11.3 (1): an R-linear functor L : FGModuleCat R ⥤ ModuleCat R
preserves finite products, see Homology, Lemma 12.3.7. This is
Functor.preservesFiniteProductsOfAdditive, using that ModuleLinear extends Additive. -/
@[stacks 06I5] #check (Functor.preservesFiniteProductsOfAdditive L : PreservesFiniteProducts L)

/- Remark 90.11.3 (2): an R-linear functor L : FGModuleCat R ⥤ ModuleCat R
sends the zero module to the zero module, see Homology, Lemma 12.3.7. This is
Functor.map_isZero. -/
@[stacks 06I5] #check (Functor.map_isZero L :
    ∀ {M : FGModuleCat.{v} R}, IsZero M → IsZero (L.obj M))
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

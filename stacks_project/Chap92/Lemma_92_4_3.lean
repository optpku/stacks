module

public import ReasLib.RingTheory.CotangentComplex.PolynomialSite
import StacksCheckRecall

/-!
# Computing the cotangent complex by derived lower shriek

Lemma 92.4.3 identifies `L_{B/A}` in `D(B)` with `Lπ!(omegaSheaf)`, recovering the source
chain `Lπ_!(Li^* Ω_{O/A}) = Lπ_!(i^* Ω_{O/A}) = Lπ_!(Ω_{O/A} ⊗_O underline{B})` as the
single existing object `omegaSheaf` placed in degree zero. Here `π` and `i` are as in
92.4.0.1, and `Lπ!` is the presheaf derived colimit of Lemma 92.4.2.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Algebra
open Algebra.PolynomialSite
open Algebra.CotangentComplex
open CommAlgCat.Over.Polynomial.Site
open scoped CategoryTheory

universe u q q'

namespace Algebra.CotangentComplex

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
variable [HasColimitsOfShape (PolynomialSite A B)ᵒᵖ (ModuleCat.{u} B)]
variable [HasDerivedCategory.{q'} (ModuleCat.{u} B)]
variable [HasDerivedCategory.{q} ((PolynomialSite A B)ᵒᵖ ⥤ ModuleCat.{u} B)]
variable [Functor.HasLeftDerivedFunctor
  (categoryOverPointColimitToDerived (PolynomialSite A B) (ModuleCat.{u} B))
  (HomotopyCategory.quasiIso ((PolynomialSite A B)ᵒᵖ ⥤ ModuleCat.{u} B)
    (ComplexShape.up ℤ))]

/- Lemma 92.4.3. Let `A → B` be a ring map, and let `π` and `i` be as in 92.4.0.1.
There is a canonical isomorphism
`DerivedCategory.Q.obj (Algebra.cotangentComplex A B) ≅
(Lπ![PolynomialSite A B, ModuleCat B]).obj (singleFunctor.obj (omegaSheaf A B))`
in `D(B)`, i.e. `L_{B/A} = Lπ_!(Li^* Ω_{O/A}) = Lπ_!(i^* Ω_{O/A}) =
Lπ_!(Ω_{O/A} ⊗_O underline{B})`. The three source presentations are the same
object: `omegaSheaf` is already the `underline{B}`-module sheaf
`i^* Ω_{O/A} = Ω_{O/A} ⊗_O underline{B}`, and `Li^* = i^*` because `Ω_{P/A}` is
free (hence flat) for each polynomial arrow `P ⟶ B`. -/
@[stacks 08PU]
#check (Algebra.CotangentComplex.lowerShriek_omega A B :
    IsIsomorphic
      (DerivedCategory.Q.obj (Algebra.cotangentComplex A B))
      ((Lπ![(PolynomialSite A B), (ModuleCat.{u} B)]).obj
        ((DerivedCategory.singleFunctor ((PolynomialSite A B)ᵒᵖ ⥤ ModuleCat.{u} B)
            (0 : ℤ)).obj (omegaSheaf A B))))

end Algebra.CotangentComplex

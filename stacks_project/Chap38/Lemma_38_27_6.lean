/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat.Flattening.Universal.Existence
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry
namespace Scheme

/- Lemma 38.27.6 (1): a finitely presented module that is pure over the base has a
universal flattening represented by a finitely presented monomorphism. -/
@[stacks 05UH] #check
  (AlgebraicGeometry.Scheme.Modules.Flattening.existsMonomorphismRepresentation_of_isPureOver :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [Scheme.Hom.FinitePresentation f]
      (ℱ : X.Modules) [ℱ.IsFinitePresentation] (_ : ℱ.IsPureOver f),
      ∃ S' : Over S,
        Nonempty ((Modules.Flattening.functor f ℱ).RepresentableBy S') ∧
          Mono S'.hom ∧ Scheme.Hom.FinitePresentation S'.hom)

/- Lemma 38.27.6 (2): a finitely presented morphism whose source is pure over the
base has a universal flattening represented by a finitely presented monomorphism. -/
@[stacks 05UH] #check
  (AlgebraicGeometry.Scheme.Flattening.existsMonomorphismRepresentation_of_isPureOver :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [Scheme.Hom.FinitePresentation f]
      (_ : Scheme.IsPureOver f),
      ∃ S' : Over S,
        Nonempty
          ((Modules.Flattening.functor f
            (SheafOfModules.unit X.ringCatSheaf : X.Modules)).RepresentableBy S') ∧
          Mono S'.hom ∧ Scheme.Hom.FinitePresentation S'.hom)

/- Lemma 38.27.6 (3): for a proper finitely presented morphism, every finitely
presented module has a universal flattening represented by a finitely presented monomorphism. -/
@[stacks 05UH] #check
  (AlgebraicGeometry.Scheme.Modules.Flattening.existsMonomorphismRepresentation_of_isProper :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f]
      [Scheme.Hom.FinitePresentation f] (ℱ : X.Modules) [ℱ.IsFinitePresentation],
      ∃ S' : Over S,
        Nonempty ((Modules.Flattening.functor f ℱ).RepresentableBy S') ∧
          Mono S'.hom ∧ Scheme.Hom.FinitePresentation S'.hom)

/- Lemma 38.27.6 (4): the universal flattening of the source of a proper finitely
presented morphism exists. -/
@[stacks 05UH] #check
  (AlgebraicGeometry.Scheme.Flattening.isRepresentable_of_isProper :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f]
      [Scheme.Hom.FinitePresentation f],
      (Modules.Flattening.functor f
        (SheafOfModules.unit X.ringCatSheaf : X.Modules)).IsRepresentable)

end Scheme
end AlgebraicGeometry

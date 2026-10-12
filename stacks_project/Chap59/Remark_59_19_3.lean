/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.SpectralSequence.Grothendieck.Existence
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe wA wB wC vA vB vC uA uB uC

/- Remark 59.19.3 (Tag 03OX): the preceding Cech-to-cohomology construction is the
   Grothendieck spectral sequence for the composition of the abelian sheaf inclusion
   `sheafToPresheaf` with the degree-zero Cech cohomology functor. -/
@[stacks 03OX] #check (CategoryTheory.Functor.RightDerived.Grothendieck.nonempty :
  ∀ {A : Type uA} {B : Type uB} {C : Type uC}
    [Category.{vA} A] [Category.{vB} B] [Category.{vC} C]
    [Abelian A] [Abelian B] [Abelian C]
    [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B] [HasDerivedCategory.{wC} C]
    [EnoughInjectives A] [EnoughInjectives B]
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]
    [Limits.PreservesFiniteLimits F] [Limits.PreservesFiniteLimits G],
    (∀ (I : A) [Injective I], Functor.RightAcyclic.Bounded G (F.obj I)) →
      ∀ (X : DerivedCategory.Plus A),
        Nonempty (Functor.RightDerived.Grothendieck.canonical F G X))

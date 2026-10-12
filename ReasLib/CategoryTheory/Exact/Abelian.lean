/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Exact.Site

@[expose] public section

/-!
# The Canonical Exact Structure on an Abelian Category

Short exact sequences form the canonical exact structure on an abelian category.  Its admissible
monomorphisms and epimorphisms are precisely the ordinary monomorphisms and epimorphisms.  The
associated singleton-epimorphism pretopology is exposed separately as the source-facing site.
-/

open CategoryTheory Limits

universe u v

namespace CategoryTheory

namespace ShortComplex.ShortExact

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- A short exact sequence in an abelian category is a kernel-cokernel pair. -/
theorem isKernelCokernelPair {S : ShortComplex A} (hS : S.ShortExact) :
    IsKernelCokernelPair S := sorry

end ShortComplex.ShortExact

namespace ExactStructure

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- For the class of short exact sequences, admissible monomorphisms are exactly ordinary
monomorphisms. -/
theorem isAdmissibleMono_shortExact_iff {X Y : A} (i : X ⟶ Y) :
    IsAdmissibleMono ({S : ShortComplex A | S.ShortExact}) i ↔ Mono i := sorry

/-- For the class of short exact sequences, admissible epimorphisms are exactly ordinary
epimorphisms. -/
theorem isAdmissibleEpi_shortExact_iff {X Y : A} (p : X ⟶ Y) :
    IsAdmissibleEpi ({S : ShortComplex A | S.ShortExact}) p ↔ Epi p := sorry

namespace ofAbelian

/-- Short exactness is invariant under isomorphisms of short complexes. -/
theorem ofIso {S T : ShortComplex A} (e : S ≅ T) :
    S.ShortExact → T.ShortExact := sorry

/-- Identities are admissible monomorphisms for the short-exact-sequence structure. -/
theorem id_admissibleMono (X : A) :
    IsAdmissibleMono ({S : ShortComplex A | S.ShortExact}) (𝟙 X) := sorry

/-- Identities are admissible epimorphisms for the short-exact-sequence structure. -/
theorem id_admissibleEpi (X : A) :
    IsAdmissibleEpi ({S : ShortComplex A | S.ShortExact}) (𝟙 X) := sorry

/-- Admissible monomorphisms for the short-exact-sequence structure are closed under
composition. -/
theorem comp_admissibleMono {X Y Z : A} {i : X ⟶ Y} {j : Y ⟶ Z}
    (hi : IsAdmissibleMono ({S : ShortComplex A | S.ShortExact}) i)
    (hj : IsAdmissibleMono ({S : ShortComplex A | S.ShortExact}) j) :
    IsAdmissibleMono ({S : ShortComplex A | S.ShortExact}) (i ≫ j) := sorry

/-- Admissible epimorphisms for the short-exact-sequence structure are closed under
composition. -/
theorem comp_admissibleEpi {X Y Z : A} {p : X ⟶ Y} {q : Y ⟶ Z}
    (hp : IsAdmissibleEpi ({S : ShortComplex A | S.ShortExact}) p)
    (hq : IsAdmissibleEpi ({S : ShortComplex A | S.ShortExact}) q) :
    IsAdmissibleEpi ({S : ShortComplex A | S.ShortExact}) (p ≫ q) := sorry

/-- Pushouts preserve admissible monomorphisms for the short-exact-sequence structure. -/
theorem pushout_admissibleMono {X Y X' : A} (i : X ⟶ Y) (f : X ⟶ X')
    (hi : IsAdmissibleMono ({S : ShortComplex A | S.ShortExact}) i) :
    ∃ (_ : HasPushout i f),
      IsAdmissibleMono ({S : ShortComplex A | S.ShortExact}) (pushout.inr i f) := sorry

/-- Pullbacks preserve admissible epimorphisms for the short-exact-sequence structure. -/
theorem pullback_admissibleEpi {Y Z Z' : A} (p : Y ⟶ Z) (f : Z' ⟶ Z)
    (hp : IsAdmissibleEpi ({S : ShortComplex A | S.ShortExact}) p) :
    ∃ (_ : HasPullback p f),
      IsAdmissibleEpi ({S : ShortComplex A | S.ShortExact}) (pullback.snd p f) := sorry

end ofAbelian

/-- The canonical exact structure on an abelian category, with short exact sequences as its
admissible kernel-cokernel pairs. -/
@[stacks 05PM "canonical exact structure"]
def ofAbelian (A : Type u) [Category.{v} A] [Abelian A] : ExactStructure A where
  admissible := {S | S.ShortExact}
  isKernelCokernelPair := ShortComplex.ShortExact.isKernelCokernelPair
  ofIso := ofAbelian.ofIso
  id_admissibleMono := ofAbelian.id_admissibleMono
  id_admissibleEpi := ofAbelian.id_admissibleEpi
  comp_admissibleMono := ofAbelian.comp_admissibleMono
  comp_admissibleEpi := ofAbelian.comp_admissibleEpi
  pushout_admissibleMono := ofAbelian.pushout_admissibleMono
  pullback_admissibleEpi := ofAbelian.pullback_admissibleEpi

/-- Admissibility in the canonical abelian exact structure is short exactness. -/
theorem ofAbelian_admissible_iff (S : ShortComplex A) :
    (ofAbelian A).admissible S ↔ S.ShortExact := sorry

/-- Admissible monomorphisms in the canonical abelian exact structure are ordinary
monomorphisms. -/
theorem ofAbelian_admissibleMono_iff {X Y : A} (i : X ⟶ Y) :
    (ofAbelian A).AdmissibleMono i ↔ Mono i := sorry

/-- Admissible epimorphisms in the canonical abelian exact structure are ordinary
epimorphisms. -/
theorem ofAbelian_admissibleEpi_iff {X Y : A} (p : X ⟶ Y) :
    (ofAbelian A).AdmissibleEpi p ↔ Epi p := sorry

end ExactStructure

namespace Abelian

variable (A : Type u) [Category.{v} A] [Abelian A]

/-- Lemma 19.9.1 (05PM): the pretopology on an abelian category whose covering presieves are
single epimorphisms. -/
@[stacks 05PM]
abbrev epiPretopology : Pretopology A :=
  (ExactStructure.ofAbelian A).singletonAdmissibleEpiPretopology

/-- The Grothendieck topology generated by singleton epimorphisms in an abelian category. -/
abbrev epiTopology : GrothendieckTopology A :=
  (ExactStructure.ofAbelian A).topology

/-- A presieve covers for `epiPretopology A` exactly when it consists of one epimorphism. -/
theorem mem_epiPretopology_iff {X : A} {S : Presieve X} :
    S ∈ epiPretopology A X ↔
      ∃ (Y : A) (p : Y ⟶ X), Epi p ∧ S = Presieve.singleton p := sorry

/-- The pretopology and coverage presentations of the epimorphism topology agree. -/
theorem epiPretopology_toGrothendieck :
    (epiPretopology A).toGrothendieck = epiTopology A := sorry

end Abelian

end CategoryTheory

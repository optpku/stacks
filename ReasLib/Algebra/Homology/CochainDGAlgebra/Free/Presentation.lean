module

public import ReasLib.Algebra.Homology.CochainDGAlgebra.Free.Words
public import ReasLib.Algebra.Homology.CochainDGAlgebra.Hom
public import ReasLib.Algebra.Homology.HomologicalComplex.Flat.ModuleCat
public import ReasLib.Algebra.Homology.HomologicalComplex.Termwise
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Free Graded-Algebra Presentations

This leaf packages a word-basis presentation of the underlying graded algebra
of a cochain differential graded algebra.
-/

noncomputable section

universe u v w x y

namespace CochainDGAlgebra.Free

variable {R : Type u} [CommRing R]

/-- A presentation of a cochain differential graded algebra whose underlying graded algebra is
free on a graded set of generators. -/
@[stacks 0BZ7 "free graded-algebra presentation"]
structure Presentation (A : CochainDGAlgebra.{u, v} R) where
  /-- The graded set of algebra generators. -/
  generators : ℤ → Type w
  /-- Each homogeneous piece has the word basis on the generators. -/
  basis (n : ℤ) : Module.Basis (WordsOfDegree generators n) R (A.toCochainComplex.X n)
  /-- The unit is the empty word. -/
  one_eq_basis : A.one = basis 0 (emptyWord generators)
  /-- Multiplication of word-basis elements is concatenation. -/
  mul_eq_basis (n m : ℤ) (x : WordsOfDegree generators n) (y : WordsOfDegree generators m) :
    A.mul n m (basis n x) (basis m y) = basis (n + m) (appendWords generators x y)

namespace Presentation

variable {A : CochainDGAlgebra.{u, v} R}

/-- A singleton graded word has the degree of its unique generator. -/
@[stacks 0BZ7 "degree of a singleton generator word"]
theorem wordDegree_singleton (P : Presentation A) {n : ℤ} (s : P.generators n) :
    wordDegree P.generators [⟨n, s⟩] = n := sorry

/-- The one-letter word associated to a homogeneous generator. -/
@[stacks 0BZ7 "singleton word of a homogeneous generator"]
def generatorWord (P : Presentation A) {n : ℤ} (s : P.generators n) :
    WordsOfDegree P.generators n :=
  ⟨[⟨n, s⟩], P.wordDegree_singleton s⟩

/-- The underlying list of a one-letter generator word. -/
@[simp, stacks 0BZ7 "underlying list of a singleton generator word"]
theorem generatorWord_val (P : Presentation A) {n : ℤ} (s : P.generators n) :
    (P.generatorWord s).1 = [⟨n, s⟩] := sorry

/-- The canonical homogeneous element represented by a generator. -/
@[stacks 0BZ7 "canonical inclusion of homogeneous generators"]
def generator (P : Presentation A) {n : ℤ} (s : P.generators n) : A.X n :=
  P.basis n (P.generatorWord s)

/-- The canonical inclusion is injective in every degree. -/
@[stacks 0BZ7 "injectivity of the homogeneous generator inclusion"]
theorem generator_injective (P : Presentation A) (n : ℤ) :
    Function.Injective (fun s : P.generators n ↦ P.generator s) := sorry

/-- A degree-preserving map from the generators of `P` to a cochain differential graded
algebra `B`. -/
@[stacks 0BZ7 "graded maps out of a presentation's generators"]
abbrev GeneratorMap (P : Presentation A) (B : CochainDGAlgebra.{u, x} R) :=
  ∀ n, P.generators n → B.X n

/-- The canonical degree-preserving family of homogeneous generator inclusions. -/
@[stacks 0BZ7 "graded family of canonical generator inclusions"]
def generatorMap (P : Presentation A) : P.GeneratorMap A :=
  fun _n s ↦ P.generator s

/-- The canonical generator family evaluates to the homogeneous generator inclusion. -/
@[simp, stacks 0BZ7 "application of the canonical generator family"]
theorem generatorMap_apply (P : Presentation A) {n : ℤ} (s : P.generators n) :
    P.generatorMap n s = P.generator s := sorry

/-- Evaluate a word in a degree-preserving family of elements of `B`. -/
@[stacks 0BZ7 "evaluation of a graded generator word"]
def wordEval (P : Presentation A) {B : CochainDGAlgebra.{u, x} R}
    (x : P.GeneratorMap B) :
    (w : List (Sigma P.generators)) → B.X (wordDegree P.generators w)
  | [] => B.one
  | ⟨n, s⟩ :: w =>
      B.mul n (wordDegree P.generators w) (x n s) (P.wordEval x w)

/-- Evaluate a homogeneous word in the homogeneous component named by its subtype index. -/
@[stacks 0BZ7 "homogeneous evaluation of a generator word"]
def wordValue (P : Presentation A) {B : CochainDGAlgebra.{u, x} R}
    (x : P.GeneratorMap B) {n : ℤ} (w : WordsOfDegree P.generators n) : B.X n :=
  cast (congrArg (fun k : ℤ ↦ (B.X k : Type x)) w.property) (P.wordEval x w.1)

/-- The homogeneous value of a singleton generator word is the assigned generator value. -/
@[simp, stacks 0BZ7 "evaluation of a singleton generator word"]
theorem wordValue_generatorWord (P : Presentation A) {B : CochainDGAlgebra.{u, x} R}
    (x : P.GeneratorMap B) {n : ℤ} (s : P.generators n) :
    P.wordValue x (P.generatorWord s) = x n s := sorry

/-- The degree-`n` linear map obtained by evaluating the word basis in `B`. -/
@[stacks 0BZ7 "linear evaluation map of a free word basis"]
def liftMap (P : Presentation A) {B : CochainDGAlgebra.{u, x} R}
    (x : P.GeneratorMap B) (n : ℤ) : A.X n →ₗ[R] B.X n :=
  (P.basis n).constr R (fun w ↦ P.wordValue x w)

/-- The graded lift map evaluates a word-basis vector by the corresponding word value. -/
@[simp, stacks 0BZ7 "graded lift map on the word basis"]
theorem liftMap_basis (P : Presentation A) {B : CochainDGAlgebra.{u, x} R}
    (x : P.GeneratorMap B) {n : ℤ} (w : WordsOfDegree P.generators n) :
    P.liftMap x n (P.basis n w) = P.wordValue x w := sorry

/-- The graded lift map preserves the unit. -/
@[simp, stacks 0BZ7 "graded lift map on the unit"]
theorem liftMap_one (P : Presentation A) {B : CochainDGAlgebra.{u, x} R}
    (x : P.GeneratorMap B) :
    P.liftMap x 0 A.one = B.one := sorry

/-- The graded lift map preserves homogeneous multiplication. -/
@[simp, stacks 0BZ7 "graded lift map on homogeneous products"]
theorem liftMap_mul (P : Presentation A) {B : CochainDGAlgebra.{u, x} R}
    (x : P.GeneratorMap B) (n m : ℤ) (a : A.X n) (b : A.X m) :
    P.liftMap x (n + m) (A.mul n m a b) =
      B.mul n m (P.liftMap x n a) (P.liftMap x m b) := sorry

/-- A graded generator map is compatible with the differentials when its induced word-basis map
commutes with the differential on the canonical generators. -/
@[stacks 0BZ7 "differential compatibility of a graded generator map"]
def IsCompatible (P : Presentation A) {B : CochainDGAlgebra.{u, x} R}
    (x : P.GeneratorMap B) : Prop :=
  ∀ n s, P.liftMap x (n + 1) (A.d n (P.generator s)) = B.d n (x n s)

/-- The word-basis evaluation map, together with differential compatibility, gives a DGA
homomorphism out of the presentation. -/
@[stacks 0BZ7 "lift of compatible graded generators"]
def lift (P : Presentation A) {B : CochainDGAlgebra.{u, x} R}
    (x : P.GeneratorMap B) (hx : P.IsCompatible x) : CochainDGAlgebra.Hom A B where
  map := P.liftMap x
  comm_d := sorry
  map_one := sorry
  map_mul := sorry

/-- The lifted homomorphism takes each canonical generator to its prescribed value. -/
@[simp, stacks 0BZ7 "lift on canonical homogeneous generators"]
theorem lift_generator (P : Presentation A) {B : CochainDGAlgebra.{u, x} R}
    (x : P.GeneratorMap B) (hx : P.IsCompatible x) (n : ℤ) (s : P.generators n) :
    P.lift x hx n (P.generator s) = x n s := sorry

/-- Restriction of a cochain-DGA homomorphism to the homogeneous generators. -/
@[stacks 0BZ7 "restriction of a cochain-DGA homomorphism to generators"]
def toGeneratorMap (P : Presentation A) {B : CochainDGAlgebra.{u, x} R}
    (f : CochainDGAlgebra.Hom A B) : P.GeneratorMap B :=
  fun n s ↦ f n (P.generator s)

/-- Restriction to generators evaluates by applying the original homomorphism to the canonical
generator. -/
@[simp, stacks 0BZ7 "restriction of a cochain-DGA homomorphism on a generator"]
theorem toGeneratorMap_apply (P : Presentation A) {B : CochainDGAlgebra.{u, x} R}
    (f : CochainDGAlgebra.Hom A B) (n : ℤ) (s : P.generators n) :
    P.toGeneratorMap f n s = f n (P.generator s) := sorry

/-- The generator values of a cochain-DGA homomorphism satisfy the presentation's differential
compatibility condition. -/
@[stacks 0BZ7 "compatibility of restricted generator values"]
theorem toGeneratorMap_isCompatible (P : Presentation A)
    {B : CochainDGAlgebra.{u, x} R} (f : CochainDGAlgebra.Hom A B) :
    P.IsCompatible (P.toGeneratorMap f) := sorry

/-- Restricting a lifted homomorphism recovers the graded generator map used to define it. -/
@[simp, stacks 0BZ7 "restriction of a lift to its generators"]
theorem toGeneratorMap_lift (P : Presentation A) {B : CochainDGAlgebra.{u, x} R}
    (x : P.GeneratorMap B) (hx : P.IsCompatible x) :
    P.toGeneratorMap (P.lift x hx) = x := sorry

/-- Postcomposition of a compatible generator map with a DGA homomorphism remains compatible. -/
@[stacks 0BZ7 "composition of compatible generator maps"]
theorem isCompatible_comp (P : Presentation A) {B : CochainDGAlgebra.{u, x} R}
    {C : CochainDGAlgebra.{u, y} R} (x : P.GeneratorMap B) (hx : P.IsCompatible x)
    (f : CochainDGAlgebra.Hom B C) :
    P.IsCompatible (fun n s ↦ f n (x n s)) := sorry

/-- Homomorphisms from a freely presented cochain-DGA are determined by their values on the
homogeneous generators. -/
@[ext, stacks 0BZ7 "extensionality for homomorphisms from a free presentation"]
theorem hom_ext (P : Presentation A) {B : CochainDGAlgebra.{u, x} R}
    {f g : CochainDGAlgebra.Hom A B}
    (h : ∀ n s, f n (P.generator s) = g n (P.generator s)) :
    f = g := sorry

/-- Every homomorphism out of a presentation is the lift of its generator values. -/
@[stacks 0BZ7 "homomorphism as the lift of its generator values"]
theorem hom_eq_lift (P : Presentation A) {B : CochainDGAlgebra.{u, x} R}
    (f : CochainDGAlgebra.Hom A B) :
    f = P.lift (P.toGeneratorMap f) (P.toGeneratorMap_isCompatible f) := sorry

/-- A compatible lift is uniquely characterized by its values on the canonical generators. -/
@[stacks 0BZ7 "uniqueness of a compatible free lift"]
theorem lift_unique (P : Presentation A) {B : CochainDGAlgebra.{u, x} R}
    (x : P.GeneratorMap B) (hx : P.IsCompatible x) (f : CochainDGAlgebra.Hom A B) :
    (∀ n s, f n (P.generator s) = x n s) ↔ f = P.lift x hx := sorry

/-- A compatible graded generator map has a unique cochain-DGA lift. -/
@[stacks 0BZ7 "existence and uniqueness of a compatible free lift"]
theorem existsUnique_lift (P : Presentation A) {B : CochainDGAlgebra.{u, x} R}
    (x : P.GeneratorMap B) (hx : P.IsCompatible x) :
    ∃! f : CochainDGAlgebra.Hom A B, ∀ n s, f n (P.generator s) = x n s := sorry

/-- Postcomposing a free lift is the lift of the postcomposed generator family. -/
@[simp, stacks 0BZ7 "composition of a free lift with a DGA homomorphism"]
theorem lift_comp (P : Presentation A) {B : CochainDGAlgebra.{u, x} R}
    {C : CochainDGAlgebra.{u, y} R} (x : P.GeneratorMap B) (hx : P.IsCompatible x)
    (f : CochainDGAlgebra.Hom B C) :
    CochainDGAlgebra.Hom.comp f (P.lift x hx) =
      P.lift (fun n s ↦ f n (x n s)) (P.isCompatible_comp x hx f) := sorry

/-- The canonical generator family satisfies the presentation's differential compatibility
condition. -/
@[stacks 0BZ7 "compatibility of the canonical generator family"]
theorem generator_isCompatible (P : Presentation A) :
    P.IsCompatible P.generatorMap := sorry

/-- Lifting the canonical generator family recovers the identity homomorphism. -/
@[stacks 0BZ7 "lift of the canonical generator family"]
theorem lift_generators (P : Presentation A) :
    P.lift P.generatorMap (P.generator_isCompatible) = CochainDGAlgebra.Hom.id A := sorry

/-- Restriction of cochain-DGA homomorphisms to the generators is injective. -/
@[stacks 0BZ7 "injectivity of restriction to free generators"]
theorem toGeneratorMap_injective (P : Presentation A) {B : CochainDGAlgebra.{u, x} R} :
    Function.Injective (fun f : CochainDGAlgebra.Hom A B ↦ P.toGeneratorMap f) := sorry

/-- A freely presented cochain differential graded algebra is termwise free over the ground
ring. -/
@[stacks 0BZ7 "termwise freeness of a free graded-algebra presentation"]
theorem isTermwiseFree (P : Presentation A) :
    A.toCochainComplex.IsTermwiseFree := sorry

/-- A freely presented cochain differential graded algebra is termwise flat over the ground
ring. -/
@[stacks 0BZ7 "termwise flatness of a free graded-algebra presentation"]
theorem isTermwiseFlat {A : CochainDGAlgebra.{u, u} R} (P : Presentation A) :
    HomologicalComplex.IsTermwiseFlat A.toCochainComplex := sorry

/-- Every homogeneous component of a free graded-algebra presentation is a free module, with no
universe restriction on the cochain-DGA carrier. -/
@[stacks 0BZ7 "degreewise freeness of a free graded-algebra presentation"]
theorem moduleFree (P : Presentation A) (n : ℤ) :
    Module.Free R (A.X n) := sorry

/-- Every homogeneous component of a free graded-algebra presentation is flat, with no universe
restriction on the cochain-DGA carrier. -/
@[stacks 0BZ7 "degreewise flatness of a free graded-algebra presentation"]
theorem moduleFlat (P : Presentation A) (n : ℤ) :
    Module.Flat R (A.X n) := sorry

end Presentation

end CochainDGAlgebra.Free

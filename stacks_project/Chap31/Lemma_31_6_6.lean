/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Pushforward.Depth
import StacksCheckRecall

@[expose] public section

open scoped ENat

noncomputable section

universe u

/- Lemma 31.6.6 (1): a point outside the image of a quasi-compact and quasi-separated morphism
is not weakly associated to the pushforward of a quasicoherent module. -/
@[stacks 0EY0] #check
  (AlgebraicGeometry.Scheme.Modules.not_mem_weakAss_pushforward_of_not_mem_range :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
      [AlgebraicGeometry.QuasiCompact f] [AlgebraicGeometry.QuasiSeparated f]
      (ℱ : X.Modules) [ℱ.IsQuasicoherent] (s : S),
      s ∉ Set.range f.base →
        s ∉ ((AlgebraicGeometry.Scheme.Modules.pushforward f).obj ℱ).weakAss)

/- Lemma 31.6.6 (2): a point outside the image is not associated to the pushforward when its
target stalk is Noetherian. -/
@[stacks 0EY0] #check
  (AlgebraicGeometry.Scheme.Modules.Pushforward.not_mem_associatedPoints_of_not_mem_range :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
      [AlgebraicGeometry.QuasiCompact f] [AlgebraicGeometry.QuasiSeparated f]
      (ℱ : X.Modules) [ℱ.IsQuasicoherent] (s : S)
      [IsNoetherianRing (S.presheaf.stalk s)],
      s ∉ Set.range f.base →
        s ∉ AlgebraicGeometry.Scheme.Modules.associatedPoints
          ((AlgebraicGeometry.Scheme.Modules.pushforward f).obj ℱ))

/- Lemma 31.6.6 (3): outside the image, a finite pushforward stalk over a Noetherian target
stalk has depth at least two. -/
@[stacks 0EY0] #check
  (AlgebraicGeometry.Scheme.Modules.Pushforward.moduleDepth_stalk_ge_two_of_not_mem_range :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
      [AlgebraicGeometry.QuasiCompact f] [AlgebraicGeometry.QuasiSeparated f]
      (ℱ : X.Modules) [ℱ.IsQuasicoherent] (s : S)
      [IsNoetherianRing (S.presheaf.stalk s)]
      [Module.Finite (S.presheaf.stalk s)
        (AlgebraicGeometry.RingedSpace.stalkModuleCat
          ((AlgebraicGeometry.Scheme.Modules.pushforward f).obj ℱ) s)],
      s ∉ Set.range f.base →
        (2 : ℕ∞) ≤ moduleDepth (S.presheaf.stalk s)
          (AlgebraicGeometry.RingedSpace.stalkModuleCat
            ((AlgebraicGeometry.Scheme.Modules.pushforward f).obj ℱ) s))

/- Lemma 31.6.6 (4): flatness over the base transfers a regular element in the target maximal
ideal to the corresponding pushforward stalk. -/
@[stacks 0EY0] #check
  (AlgebraicGeometry.Scheme.Modules.Pushforward.isSMulRegular_stalk_of_flatOver :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
      [AlgebraicGeometry.QuasiCompact f] [AlgebraicGeometry.QuasiSeparated f]
      (ℱ : X.Modules) [ℱ.IsQuasicoherent]
      (_ : AlgebraicGeometry.Scheme.Modules.flatOver ℱ f)
      (s : S) (a : S.presheaf.stalk s),
      a ∈ IsLocalRing.maximalIdeal (S.presheaf.stalk s) →
        IsSMulRegular (S.presheaf.stalk s) a →
          IsSMulRegular
            (AlgebraicGeometry.RingedSpace.stalkModuleCat
              ((AlgebraicGeometry.Scheme.Modules.pushforward f).obj ℱ) s) a)

/- Lemma 31.6.6 (5), first conclusion: for a regular pair in the target maximal ideal and a
module flat over the base, the first element acts regularly on the pushforward stalk. -/
@[stacks 0EY0] #check
  (AlgebraicGeometry.Scheme.Modules.Pushforward.isSMulRegular_stalk_first_of_flatOver_of_isRegular_pair :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
      [AlgebraicGeometry.QuasiCompact f] [AlgebraicGeometry.QuasiSeparated f]
      (ℱ : X.Modules) [ℱ.IsQuasicoherent]
      (_ : AlgebraicGeometry.Scheme.Modules.flatOver ℱ f)
      (s : S) (a b : S.presheaf.stalk s),
      a ∈ IsLocalRing.maximalIdeal (S.presheaf.stalk s) →
        b ∈ IsLocalRing.maximalIdeal (S.presheaf.stalk s) →
          RingTheory.Sequence.IsRegular (S.presheaf.stalk s) [a, b] →
            IsSMulRegular
              (AlgebraicGeometry.RingedSpace.stalkModuleCat
                ((AlgebraicGeometry.Scheme.Modules.pushforward f).obj ℱ) s) a)

/- Lemma 31.6.6 (5), second conclusion: for a regular pair in the target maximal ideal and a
module flat over the base, the second element acts regularly after quotienting the pushforward
stalk by the first. -/
@[stacks 0EY0] #check
  (AlgebraicGeometry.Scheme.Modules.Pushforward.isSMulRegular_quotSMulTop_stalk_second_of_flatOver_of_isRegular_pair :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
      [AlgebraicGeometry.QuasiCompact f] [AlgebraicGeometry.QuasiSeparated f]
      (ℱ : X.Modules) [ℱ.IsQuasicoherent]
      (_ : AlgebraicGeometry.Scheme.Modules.flatOver ℱ f)
      (s : S) (a b : S.presheaf.stalk s),
      a ∈ IsLocalRing.maximalIdeal (S.presheaf.stalk s) →
        b ∈ IsLocalRing.maximalIdeal (S.presheaf.stalk s) →
          RingTheory.Sequence.IsRegular (S.presheaf.stalk s) [a, b] →
            IsSMulRegular
              (QuotSMulTop a
                (AlgebraicGeometry.RingedSpace.stalkModuleCat
                  ((AlgebraicGeometry.Scheme.Modules.pushforward f).obj ℱ) s)) b)

/- Lemma 31.6.6 (6): if a quasicoherent module is flat over the base and its pushforward stalk
is finite, that stalk has depth at least the minimum of two and the depth of the target ring. -/
@[stacks 0EY0] #check
  (AlgebraicGeometry.Scheme.Modules.Pushforward.moduleDepth_stalk_ge_min_two_of_flatOver :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
      [AlgebraicGeometry.QuasiCompact f] [AlgebraicGeometry.QuasiSeparated f]
      (ℱ : X.Modules) [ℱ.IsQuasicoherent]
      (_ : AlgebraicGeometry.Scheme.Modules.flatOver ℱ f) (s : S)
      [Module.Finite (S.presheaf.stalk s)
        (AlgebraicGeometry.RingedSpace.stalkModuleCat
          ((AlgebraicGeometry.Scheme.Modules.pushforward f).obj ℱ) s)],
      min (2 : ℕ∞) (moduleDepth (S.presheaf.stalk s) (S.presheaf.stalk s)) ≤
        moduleDepth (S.presheaf.stalk s)
          (AlgebraicGeometry.RingedSpace.stalkModuleCat
            ((AlgebraicGeometry.Scheme.Modules.pushforward f).obj ℱ) s))

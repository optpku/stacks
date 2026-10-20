/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.RingHom.IndZariski.Profinite
public import ReasLib.RingTheory.RingHom.IndZariski.FunctionColimit
import StacksCheckRecall

/-!
# Example 61.6.3

A field map realizing a prescribed profinite space as a spectrum, via the
function-ring colimit on discrete quotients or any finite inverse-limit presentation.
-/

@[expose] public section

universe u v w x

open CategoryTheory Limits

namespace RingHom.IndZariski

/- Example 61.6.3 (1): if `k` is a field and `T` is a profinite space, there
exists an ind-Zariski ring map `f : k →+* A` such that `PrimeSpectrum A` is
homeomorphic to `T`. -/
@[stacks 09BJ]
#check (RingHom.IndZariski.exists_of_profinite :
  ∀ {k : Type u} [Field k] {T : Type v}
    [TopologicalSpace T] [CompactSpace T] [T2Space T] [TotallyDisconnectedSpace T],
    ∃ (A : Type (max u v)) (_ : CommRing A) (f : k →+* A) (_ : PrimeSpectrum A ≃ₜ T),
      f.IndZariski)

/- Example 61.6.3 (2): writing `T` as the filtered limit of its finite discrete
quotients `S`, the colimit `A = functionColimit k T` of the function rings
`S → k` receives an ind-Zariski map from `k`, and `PrimeSpectrum A` is
homeomorphic to `T`. -/
@[stacks 09BJ]
#check (RingHom.IndZariski.functionColimit_spec :
  ∀ {k : Type u} [Field k] {T : Type v}
    [TopologicalSpace T] [CompactSpace T] [T2Space T] [TotallyDisconnectedSpace T],
    (RingHom.IndZariski.algebraMap_functionColimit k T).IndZariski ∧
      Nonempty (PrimeSpectrum (RingHom.IndZariski.functionColimit k T) ≃ₜ T))

/- Example 61.6.3 (3): for any presentation of a profinite space as a cofiltered
limit of finite spaces, `functionColimit k c.pt` is the colimit of the stage
function rings, with canonical stage maps induced by the cone projections. -/
@[stacks 09BJ]
#check (RingHom.IndZariski.functionColimit.existsUnique_desc_of_isLimit :
  ∀ (k : Type u) [Field k] {J : Type w} [SmallCategory J] [IsCofiltered J]
    (F : J ⥤ Profinite.{v}) [∀ j, _root_.Finite (F.obj j)]
    (c : Cone F) (_ : IsLimit c) (B : Type x) [CommRing B]
    (g : ∀ j, (F.obj j → k) →+* B),
    (∀ {i j : J} (a : i ⟶ j),
      (g i).comp (RingHom.IndZariski.functionRingMap (F.map a)) = g j) →
    ∃! desc : RingHom.IndZariski.functionColimit k c.pt →+* B,
      ∀ j, desc.comp
        (RingHom.IndZariski.functionColimit.ofFinite k (c.π.app j).hom.hom) = g j)

end RingHom.IndZariski

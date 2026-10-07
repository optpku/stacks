module

public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Limits.Cones
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.Data.Countable.Small
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap65.Lemma_65_8_4_Coproduct
public import stacks_project.Chap65.Lemma_65_12_4_Immersion
public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap67.Lemma_67_13_5_Complement
public import stacks_project.Chap67.Lemma_67_40_3_Pullback
public import stacks_project.Chap67.Lemma_67_40_4
public import stacks_project.Chap67.Definition_67_48_3_IntegralClosure
public import stacks_project.Chap67.Definition_67_48_3_RelativeSpectrum
public import stacks_project.Chap67.Lemma_67_53_4_UniversalHomeomorphism
public import stacks_project.Chap70.Lemma_70_19_1_IsoOverOpen
public import stacks_project.Chap76.Definition_76_6_5_NormalCone
public import stacks_project.Chap76.Definition_76_12_1_Neighbourhood
public import stacks_project.Chap76.Lemma_76_6_3_Map

/-!
# Sequential coequalizer glueing of algebraic spaces

In the proper-iso-over-complement situation, the infinitesimal neighbourhoods
of a closed immersion, coproduct with a proper morphism, and kernel-pair
equalizer algebras assemble into a sequential system of relative spectra over
the ambient space.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.CoequalizerGlueing

variable {S : Scheme.{u}} {X X' Z : AlgebraicSpace S}

/-- The defining ideal of the `(n + 1)`st infinitesimal neighbourhood is contained
in the defining ideal of the `n`th neighbourhood. -/
theorem ideal_succ_le (i : Z ⟶ X) [IsImmersion i] (n : ℕ) :
    Hom.InfinitesimalNeighbourhood.ideal i (n + 1) ≤
      Hom.InfinitesimalNeighbourhood.ideal i n :=
  sorry

/-- The closed-subspace transition from the `n`th infinitesimal neighbourhood to
the `(n + 1)`st neighbourhood. -/
def neighbourhoodSucc (i : Z ⟶ X) [IsImmersion i] (n : ℕ) :
    Hom.InfinitesimalNeighbourhood.space i n ⟶
      Hom.InfinitesimalNeighbourhood.space i (n + 1) :=
  subschemeInclusion (ideal_succ_le i n)

/-- The two-element family whose coproduct is `X' ⨿` the `n`th infinitesimal
neighbourhood of `i`. -/
def summandFamily (f : X' ⟶ X) (i : Z ⟶ X) [IsClosedImmersion i] (n : ℕ)
    (b : Bool) : AlgebraicSpace S :=
  match b with
  | false => X'
  | true => Hom.InfinitesimalNeighbourhood.space i n

/-- The `false` summand of the neighbourhood coproduct family is `X'`. -/
theorem summandFamily_false (f : X' ⟶ X) (i : Z ⟶ X) [IsClosedImmersion i] (n : ℕ) :
    summandFamily f i n false = X' :=
  rfl

/-- The `true` summand of the neighbourhood coproduct family is the `n`th
infinitesimal neighbourhood of `i`. -/
theorem summandFamily_true (f : X' ⟶ X) (i : Z ⟶ X) [IsClosedImmersion i] (n : ℕ) :
    summandFamily f i n true = Hom.InfinitesimalNeighbourhood.space i n :=
  rfl

/-- The coproduct `Y_{n+1} = X' ⨿ Z_{n+1}` of the proper source with the `n`th
infinitesimal neighbourhood, as an algebraic space over `S`. -/
def summand (f : X' ⟶ X) (i : Z ⟶ X) [IsClosedImmersion i] (n : ℕ) : AlgebraicSpace S :=
  coproduct (summandFamily f i n)

/-- The neighbourhood coproduct is the sheaf coproduct of `summandFamily`. -/
theorem summand_eq_coproduct (f : X' ⟶ X) (i : Z ⟶ X) [IsClosedImmersion i] (n : ℕ) :
    summand f i n = coproduct (summandFamily f i n) :=
  rfl

/-- The structure morphism `g_n : Y_{n+1} ⟶ X` of the neighbourhood coproduct. -/
def summandToAmbient (f : X' ⟶ X) (i : Z ⟶ X) [IsClosedImmersion i] (n : ℕ) :
    summand f i n ⟶ X :=
  coproductDesc fun b ↦
    match b with
    | false => (f : summandFamily f i n false ⟶ X)
    | true => Hom.InfinitesimalNeighbourhood.toAmbient i n

/-- The coproduct inclusion of `X'` recovers `f` after composing with
`summandToAmbient`. -/
theorem coproductι_summandToAmbient_false (f : X' ⟶ X) (i : Z ⟶ X)
    [IsClosedImmersion i] (n : ℕ) :
    coproductι (summandFamily f i n) false ≫ summandToAmbient f i n = f :=
  sorry

/-- The coproduct inclusion of the infinitesimal neighbourhood recovers
`Hom.InfinitesimalNeighbourhood.toAmbient` after composing with
`summandToAmbient`. -/
theorem coproductι_summandToAmbient_true (f : X' ⟶ X) (i : Z ⟶ X)
    [IsClosedImmersion i] (n : ℕ) :
    coproductι (summandFamily f i n) true ≫ summandToAmbient f i n =
      Hom.InfinitesimalNeighbourhood.toAmbient i n :=
  sorry

/-- The neighbourhood-coproduct structure morphism is proper. -/
instance instProper_summandToAmbient (f : X' ⟶ X) (i : Z ⟶ X)
    [IsClosedImmersion i] [Proper f] (n : ℕ) :
    Proper (summandToAmbient f i n) :=
  sorry

/-- The successor map `Y_{n+1} ⟶ Y_{n+2}` of neighbourhood coproducts. -/
def summandSucc (f : X' ⟶ X) (i : Z ⟶ X) [IsClosedImmersion i] (n : ℕ) :
    summand f i n ⟶ summand f i (n + 1) :=
  coproductDesc fun b ↦
    match b with
    | false =>
        (coproductι (summandFamily f i (n + 1)) false :
          summandFamily f i n false ⟶ summand f i (n + 1))
    | true => neighbourhoodSucc i n ≫ coproductι (summandFamily f i (n + 1)) true

/-- The successor of neighbourhood coproducts lies over `X`. -/
theorem summandSucc_comp (f : X' ⟶ X) (i : Z ⟶ X) [IsClosedImmersion i] (n : ℕ) :
    summandSucc f i n ≫ summandToAmbient f i (n + 1) = summandToAmbient f i n :=
  sorry

/-- The composite of the neighbourhood-coproduct successor with the next structure
morphism is proper. -/
instance instProper_summandSucc_comp (f : X' ⟶ X) (i : Z ⟶ X)
    [IsClosedImmersion i] [Proper f] (n : ℕ) :
    Proper (summandSucc f i n ≫ summandToAmbient f i (n + 1)) :=
  sorry

/-- The kernel pair `R_n = Y_{n+1} ×_X Y_{n+1}` of the neighbourhood-coproduct
structure morphism. -/
def relation (f : X' ⟶ X) (i : Z ⟶ X) [IsClosedImmersion i] (n : ℕ) : AlgebraicSpace S :=
  pullback (summandToAmbient f i n) (summandToAmbient f i n)

/-- The neighbourhood relation is the kernel pair of `summandToAmbient`. -/
theorem relation_eq_pullback (f : X' ⟶ X) (i : Z ⟶ X) [IsClosedImmersion i] (n : ℕ) :
    relation f i n = pullback (summandToAmbient f i n) (summandToAmbient f i n) :=
  rfl

/-- The first projection of the neighbourhood kernel pair. -/
def relationFst (f : X' ⟶ X) (i : Z ⟶ X) [IsClosedImmersion i] (n : ℕ) :
    relation f i n ⟶ summand f i n :=
  pullback.fst (summandToAmbient f i n) (summandToAmbient f i n)

/-- The second projection of the neighbourhood kernel pair. -/
def relationSnd (f : X' ⟶ X) (i : Z ⟶ X) [IsClosedImmersion i] (n : ℕ) :
    relation f i n ⟶ summand f i n :=
  pullback.snd (summandToAmbient f i n) (summandToAmbient f i n)

/-- The structure morphism `h_n : R_n ⟶ X` of the neighbourhood kernel pair. -/
def relationToAmbient (f : X' ⟶ X) (i : Z ⟶ X) [IsClosedImmersion i] (n : ℕ) :
    relation f i n ⟶ X :=
  relationSnd f i n ≫ summandToAmbient f i n

/-- The neighbourhood kernel-pair structure morphism is proper. -/
instance instProper_relationToAmbient (f : X' ⟶ X) (i : Z ⟶ X)
    [IsClosedImmersion i] [Proper f] (n : ℕ) :
    Proper (relationToAmbient f i n) :=
  sorry

/-- The successor map of neighbourhood kernel pairs, induced by `summandSucc`. -/
def relationSucc (f : X' ⟶ X) (i : Z ⟶ X) [IsClosedImmersion i] (n : ℕ) :
    relation f i n ⟶ relation f i (n + 1) :=
  pullback.map
    (summandToAmbient f i n) (summandToAmbient f i n)
    (summandToAmbient f i (n + 1)) (summandToAmbient f i (n + 1))
    (summandSucc f i n) (summandSucc f i n) (𝟙 X) sorry sorry

/-- The algebra map `g_n,* 𝒪_{Y_{n+1}} ⟶ h_n,* 𝒪_{R_n}` induced by the first
kernel-pair projection. -/
def algebraMapFst (f : X' ⟶ X) (i : Z ⟶ X) [IsClosedImmersion i] [Proper f] (n : ℕ) :
    (pushforwardStructureQcAlgebra (summandToAmbient f i n)).obj.right ⟶
      (pushforwardStructureQcAlgebra (relationToAmbient f i n)).obj.right :=
  (commRingPushforward (summandToAmbient f i n)).map
      (commRingStructureSheafMap (relationFst f i n)) ≫
    (ConormalAlgebra.commRingPushforwardCompIso
        (relationFst f i n) (summandToAmbient f i n)).hom.app
      (commRingStructureSheaf (relation f i n)) ≫
    eqToHom
      (congrArg
        (fun p ↦ (commRingPushforward p).obj (commRingStructureSheaf (relation f i n)))
        (pullback.condition :
          relationFst f i n ≫ summandToAmbient f i n =
            relationSnd f i n ≫ summandToAmbient f i n))

/-- The algebra map `g_n,* 𝒪_{Y_{n+1}} ⟶ h_n,* 𝒪_{R_n}` induced by the second
kernel-pair projection. -/
def algebraMapSnd (f : X' ⟶ X) (i : Z ⟶ X) [IsClosedImmersion i] [Proper f] (n : ℕ) :
    (pushforwardStructureQcAlgebra (summandToAmbient f i n)).obj.right ⟶
      (pushforwardStructureQcAlgebra (relationToAmbient f i n)).obj.right :=
  (commRingPushforward (summandToAmbient f i n)).map
      (commRingStructureSheafMap (relationSnd f i n)) ≫
    (ConormalAlgebra.commRingPushforwardCompIso
        (relationSnd f i n) (summandToAmbient f i n)).hom.app
      (commRingStructureSheaf (relation f i n))

/-- The pointwise equalizer of the two kernel-pair algebra maps, as a
commutative-ring presheaf on the small étale site of `X`. -/
def equalizerPresheaf (f : X' ⟶ X) (i : Z ⟶ X) [IsClosedImmersion i] [Proper f] (n : ℕ) :
    (smallEtaleSite X)ᵒᵖ ⥤ CommRingCat.{u} where
  obj U := equalizer ((algebraMapFst f i n).hom.app U) ((algebraMapSnd f i n).hom.app U)
  map {U V} iUV :=
    equalizer.lift
      (equalizer.ι ((algebraMapFst f i n).hom.app U) ((algebraMapSnd f i n).hom.app U) ≫
        (pushforwardStructureQcAlgebra (summandToAmbient f i n)).obj.right.obj.map iUV)
      sorry
  map_id := sorry
  map_comp := sorry

/-- The equalizer of the kernel-pair algebra maps, as a sheaf of commutative
rings on the small étale site of `X`. -/
def equalizerSheaf (f : X' ⟶ X) (i : Z ⟶ X) [IsClosedImmersion i] [Proper f] (n : ℕ) :
    Sheaf (smallEtaleTopology X) CommRingCat.{u} where
  obj := equalizerPresheaf f i n
  property := sorry

/-- The structure map `𝒪_X ⟶` the kernel-pair equalizer sheaf. -/
def equalizerStructureMap (f : X' ⟶ X) (i : Z ⟶ X) [IsClosedImmersion i] [Proper f]
    (n : ℕ) : commRingStructureSheaf X ⟶ equalizerSheaf f i n :=
  InducedCategory.homMk
    { app := fun U ↦
        equalizer.lift
          ((commRingStructureSheafMap (summandToAmbient f i n)).hom.app U) sorry
      naturality := sorry }

/-- The quasi-coherent `𝒪_X`-algebra `𝒜_{n+1}` equalizing the two kernel-pair
algebra maps of `g_n`. -/
def equalizerAlgebra (f : X' ⟶ X) (i : Z ⟶ X) [IsClosedImmersion i] [Proper f]
    (n : ℕ) : X.QcAlgebraUnder where
  obj := Under.mk (equalizerStructureMap f i n)
  property := sorry

/-- The two kernel-pair algebra maps agree after restriction to the equalizer
sheaf of `equalizerAlgebra`. -/
theorem equalizerAlgebra_spec (f : X' ⟶ X) (i : Z ⟶ X) [IsClosedImmersion i]
    [Proper f] (n : ℕ) (U : (smallEtaleSite X)ᵒᵖ) :
    equalizer.ι ((algebraMapFst f i n).hom.app U) ((algebraMapSnd f i n).hom.app U) ≫
        (algebraMapFst f i n).hom.app U =
      equalizer.ι ((algebraMapFst f i n).hom.app U) ((algebraMapSnd f i n).hom.app U) ≫
        (algebraMapSnd f i n).hom.app U :=
  sorry

/-- The coequalizer stage `X_{n+1}` of `s, t : R_n ⇉ Y_{n+1}`, as the relative
spectrum of the kernel-pair equalizer algebra. -/
def stage (f : X' ⟶ X) (i : Z ⟶ X) [IsClosedImmersion i] [Proper f] (n : ℕ) :
    AlgebraicSpace S :=
  relativeSpec (equalizerAlgebra f i n)

/-- The coequalizer stage is the relative spectrum of `equalizerAlgebra`. -/
theorem stage_eq_relativeSpec (f : X' ⟶ X) (i : Z ⟶ X) [IsClosedImmersion i]
    [Proper f] (n : ℕ) :
    stage f i n = relativeSpec (equalizerAlgebra f i n) :=
  rfl

/-- The structure morphism `X_{n+1} ⟶ X` of a coequalizer stage. -/
def toAmbient (f : X' ⟶ X) (i : Z ⟶ X) [IsClosedImmersion i] [Proper f]
    (h_iso : IsIsoOverOpen f (closedImmersionComplementι i)) (n : ℕ) :
    stage f i n ⟶ X :=
  relativeSpecπ (equalizerAlgebra f i n)

/-- The structure morphism of a coequalizer stage is the relative-spectrum
projection of `equalizerAlgebra`. -/
theorem toAmbient_eq_relativeSpecπ (f : X' ⟶ X) (i : Z ⟶ X) [IsClosedImmersion i]
    [Proper f] (h_iso : IsIsoOverOpen f (closedImmersionComplementι i)) (n : ℕ) :
    toAmbient f i h_iso n = relativeSpecπ (equalizerAlgebra f i n) :=
  rfl

/-- Direct image along the neighbourhood-coproduct successor, as a map of
pushforward algebras over `X`. -/
def summandPushforwardMap (f : X' ⟶ X) (i : Z ⟶ X) [IsClosedImmersion i] [Proper f]
    (n : ℕ) :
    (pushforwardStructureQcAlgebra (summandToAmbient f i (n + 1))).obj.right ⟶
      (pushforwardStructureQcAlgebra
        (summandSucc f i n ≫ summandToAmbient f i (n + 1))).obj.right :=
  (commRingPushforward (summandToAmbient f i (n + 1))).map
      (commRingStructureSheafMap (summandSucc f i n)) ≫
    (ConormalAlgebra.commRingPushforwardCompIso
        (summandSucc f i n) (summandToAmbient f i (n + 1))).hom.app
      (commRingStructureSheaf (summand f i n))

/-- The morphism of equalizer algebras `𝒜_{n+2} ⟶ 𝒜_{n+1}` induced by
`Y_{n+1} ⟶ Y_{n+2}` over `X`. -/
def algebraTransition (f : X' ⟶ X) (i : Z ⟶ X) [IsClosedImmersion i] [Proper f]
    (n : ℕ) : equalizerAlgebra f i (n + 1) ⟶ equalizerAlgebra f i n :=
  InducedCategory.homMk
    (Under.homMk
      (InducedCategory.homMk
        { app := fun U ↦
            equalizer.lift
              (equalizer.ι
                  ((algebraMapFst f i (n + 1)).hom.app U)
                  ((algebraMapSnd f i (n + 1)).hom.app U) ≫
                (summandPushforwardMap f i n).hom.app U ≫
                  eqToHom
                    (congrArg
                      (fun p ↦
                        ((commRingPushforward p).obj
                            (commRingStructureSheaf (summand f i n))).obj.obj U)
                      (summandSucc_comp f i n)))
              sorry
          naturality := sorry })
      sorry)

/-- The successor morphism `X_{n+1} ⟶ X_{n+2}` of coequalizer stages. -/
def stageMap (f : X' ⟶ X) (i : Z ⟶ X) [IsClosedImmersion i] [Proper f]
    (h_iso : IsIsoOverOpen f (closedImmersionComplementι i)) (n : ℕ) :
    stage f i n ⟶ stage f i (n + 1) :=
  relativeSpecMap (algebraTransition f i n)

/-- The sequential system `X_1 ⟶ X_2 ⟶ X_3 ⟶ ⋯` of coequalizer stages. -/
def system (f : X' ⟶ X) (i : Z ⟶ X) [IsLocallyNoetherian X] [IsClosedImmersion i]
    [Proper f] (h_iso : IsIsoOverOpen f (closedImmersionComplementι i)) :
    ℕ ⥤ AlgebraicSpace S :=
  Functor.ofSequence (stageMap f i h_iso)

/-- The objects of the coequalizer system are the relative-spectrum stages. -/
theorem system_obj (f : X' ⟶ X) (i : Z ⟶ X) [IsLocallyNoetherian X]
    [IsClosedImmersion i] [Proper f]
    (h_iso : IsIsoOverOpen f (closedImmersionComplementι i)) (n : ℕ) :
    (system f i h_iso).obj n = stage f i n :=
  rfl

/-- Successor morphisms of the coequalizer system are the stage maps. -/
theorem system_map_succ (f : X' ⟶ X) (i : Z ⟶ X) [IsLocallyNoetherian X]
    [IsClosedImmersion i] [Proper f]
    (h_iso : IsIsoOverOpen f (closedImmersionComplementι i)) (n : ℕ) :
    (system f i h_iso).map (homOfLE n.le_succ) = stageMap f i h_iso n :=
  sorry

/-- The successor stage map lies over `X`. -/
theorem toAmbient_comp_stageMap (f : X' ⟶ X) (i : Z ⟶ X) [IsClosedImmersion i]
    [Proper f] (h_iso : IsIsoOverOpen f (closedImmersionComplementι i)) (n : ℕ) :
    stageMap f i h_iso n ≫ toAmbient f i h_iso (n + 1) = toAmbient f i h_iso n :=
  sorry

/-- The cocone of coequalizer stages with vertex `X`. -/
def cocone (f : X' ⟶ X) (i : Z ⟶ X) [IsLocallyNoetherian X] [IsClosedImmersion i]
    [Proper f] (h_iso : IsIsoOverOpen f (closedImmersionComplementι i)) :
    Cocone (system f i h_iso) where
  pt := X
  ι := NatTrans.ofSequence (toAmbient f i h_iso) fun _ ↦ sorry

/-- The coequalizer-stage structure morphisms to `X` are universal homeomorphisms. -/
instance instUniversalHomeomorphism_toAmbient (f : X' ⟶ X) (i : Z ⟶ X)
    [IsLocallyNoetherian X] [IsClosedImmersion i] [Proper f]
    (h_iso : IsIsoOverOpen f (closedImmersionComplementι i)) (n : ℕ) :
    UniversalHomeomorphism (toAmbient f i h_iso n) :=
  sorry

/-- The successor morphisms of coequalizer stages are universal homeomorphisms. -/
instance instUniversalHomeomorphism_stageMap (f : X' ⟶ X) (i : Z ⟶ X)
    [IsLocallyNoetherian X] [IsClosedImmersion i] [Proper f]
    (h_iso : IsIsoOverOpen f (closedImmersionComplementι i)) (n : ℕ) :
    UniversalHomeomorphism (stageMap f i h_iso n) :=
  sorry

/-- The Stacks-indexed infinitesimal neighbourhood `Z_n = V(I^n)` for `n ≥ 1`,
as `Hom.InfinitesimalNeighbourhood.space i (n - 1)` since `space i k` is cut
out by `I^{k+1}`. -/
def neighbourhoodOf (i : Z ⟶ X) [IsClosedImmersion i] (n : ℕ) [NeZero n] :
    AlgebraicSpace S :=
  Hom.InfinitesimalNeighbourhood.space i n.pred

/-- The Stacks-indexed neighbourhood `Z_n` is the `(n - 1)`st infinitesimal
neighbourhood space. -/
theorem neighbourhoodOf_eq_space (i : Z ⟶ X) [IsClosedImmersion i] (n : ℕ)
    [NeZero n] :
    neighbourhoodOf i n = Hom.InfinitesimalNeighbourhood.space i n.pred :=
  rfl

/-- The Stacks-indexed coequalizer stage `X_n` for `n ≥ 1`. -/
def stageOf (f : X' ⟶ X) (i : Z ⟶ X) [IsClosedImmersion i] [Proper f] (n : ℕ)
    [NeZero n] : AlgebraicSpace S :=
  stage f i n.pred

/-- The Stacks-indexed stage `X_n` is the `(n - 1)`st relative-spectrum stage. -/
theorem stageOf_eq_stage (f : X' ⟶ X) (i : Z ⟶ X) [IsClosedImmersion i]
    [Proper f] (n : ℕ) [NeZero n] :
    stageOf f i n = stage f i n.pred :=
  rfl

end AlgebraicGeometry.AlgebraicSpace.CoequalizerGlueing

/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import stacks_project.Chap66.«66_26_0_1_Pushforward»
public import stacks_project.Chap66.Lemma_66_29_7_Quasicoherent
public import stacks_project.Chap67.Lemma_67_28_8_FinitePresentation
public import stacks_project.Chap81.«81_10_6_1_Glueing»

/-!
# Reverse functor for formal glueing of quasi-coherent modules

The reverse assignment on a glueing triple `(H, G, φ)` is the kernel of the
comparison `j_* H ⊞ f_* G ⟶ (f ∘ j')_* (G|_V)` in `X.Modules`. Under the
standing qcqs and finite-presentation hypotheses this kernel is quasi-coherent,
and the assignment is a functor `QCoh(Y → X, Z) ⥤ QCoh X`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.ObjectProperty
open CategoricalPullback

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.QCoh.FormalGlueing

/-- The `H`-leg of the reverse comparison: push the glueing isomorphism forward
along `f|_V` after the pullback–pushforward unit, identify successive
pushforwards with pushforward of the composite, and rewrite the composite along
`restrict_comp`. -/
def fromH {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : Y ⟶ X) (i : Z ⟶ X)
    [IsClosedImmersion i] (T : category f i) :
    (Modules.pushforward (closedImmersionComplementι i)).obj T.fst.obj ⟶
      (Modules.pushforward
          (closedImmersionComplementι (inverseImageι f i) ≫ f)).obj
        ((Modules.pullback (closedImmersionComplementι (inverseImageι f i))).obj
          T.snd.obj) :=
  (Modules.pushforward (closedImmersionComplementι i)).map
      ((Modules.pullbackPushforwardAdjunction (restrict f i)).unit.app T.fst.obj ≫
        (Modules.pushforward (restrict f i)).map T.iso.hom.hom) ≫
    (Modules.pushforwardComp (restrict f i)
        (closedImmersionComplementι i)).hom.app
      ((Modules.pullback (closedImmersionComplementι (inverseImageι f i))).obj
        T.snd.obj) ≫
    eqToHom
      (congrArg
        (fun g : closedImmersionComplement (inverseImageι f i) ⟶ X ↦
          (Modules.pushforward g).obj
            ((Modules.pullback
                (closedImmersionComplementι (inverseImageι f i))).obj T.snd.obj))
        (restrict_comp f i))

/-- `fromH` is the unit-then-glueing-isomorphism pushforward, transported along
`pushforwardComp` and `restrict_comp`. -/
theorem fromH_eq {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : Y ⟶ X)
    (i : Z ⟶ X) [IsClosedImmersion i] (T : category f i) :
    fromH f i T =
      (Modules.pushforward (closedImmersionComplementι i)).map
          ((Modules.pullbackPushforwardAdjunction (restrict f i)).unit.app
              T.fst.obj ≫
            (Modules.pushforward (restrict f i)).map T.iso.hom.hom) ≫
        (Modules.pushforwardComp (restrict f i)
            (closedImmersionComplementι i)).hom.app
          ((Modules.pullback
              (closedImmersionComplementι (inverseImageι f i))).obj T.snd.obj) ≫
        eqToHom
          (congrArg
            (fun g : closedImmersionComplement (inverseImageι f i) ⟶ X ↦
              (Modules.pushforward g).obj
                ((Modules.pullback
                    (closedImmersionComplementι (inverseImageι f i))).obj
                  T.snd.obj))
            (restrict_comp f i)) :=
  rfl

/-- The `G`-leg of the reverse comparison: push the pullback–pushforward unit of
`j'` forward along `f`, then identify successive pushforwards with
`(f ∘ j')_*`. -/
def fromG {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : Y ⟶ X) (i : Z ⟶ X)
    [IsClosedImmersion i] (T : category f i) :
    (Modules.pushforward f).obj T.snd.obj ⟶
      (Modules.pushforward
          (closedImmersionComplementι (inverseImageι f i) ≫ f)).obj
        ((Modules.pullback (closedImmersionComplementι (inverseImageι f i))).obj
          T.snd.obj) :=
  (Modules.pushforward f).map
      ((Modules.pullbackPushforwardAdjunction
          (closedImmersionComplementι (inverseImageι f i))).unit.app T.snd.obj) ≫
    (Modules.pushforwardComp
        (closedImmersionComplementι (inverseImageι f i)) f).hom.app
      ((Modules.pullback (closedImmersionComplementι (inverseImageι f i))).obj
        T.snd.obj)

/-- `fromG` is the restriction-unit pushforward, transported along
`pushforwardComp`. -/
theorem fromG_eq {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : Y ⟶ X)
    (i : Z ⟶ X) [IsClosedImmersion i] (T : category f i) :
    fromG f i T =
      (Modules.pushforward f).map
          ((Modules.pullbackPushforwardAdjunction
              (closedImmersionComplementι (inverseImageι f i))).unit.app
            T.snd.obj) ≫
        (Modules.pushforwardComp
            (closedImmersionComplementι (inverseImageι f i)) f).hom.app
          ((Modules.pullback
              (closedImmersionComplementι (inverseImageι f i))).obj T.snd.obj) :=
  rfl

/-- The reverse comparison `j_* H ⊞ f_* G ⟶ (f ∘ j')_* (G|_V)`, as the copairing
of the `H`-leg and the negated `G`-leg. -/
def comparison {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : Y ⟶ X)
    (i : Z ⟶ X) [IsClosedImmersion i] (T : category f i) :
    (Modules.pushforward (closedImmersionComplementι i)).obj T.fst.obj ⊞
        (Modules.pushforward f).obj T.snd.obj ⟶
      (Modules.pushforward
          (closedImmersionComplementι (inverseImageι f i) ≫ f)).obj
        ((Modules.pullback (closedImmersionComplementι (inverseImageι f i))).obj
          T.snd.obj) :=
  biprod.desc (fromH f i T) (-fromG f i T)

/-- `comparison` is the biproduct copairing of `fromH` and `-fromG`. -/
theorem comparison_eq {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : Y ⟶ X)
    (i : Z ⟶ X) [IsClosedImmersion i] (T : category f i) :
    comparison f i T = biprod.desc (fromH f i T) (-fromG f i T) :=
  rfl

/-- The reverse kernel of a quasi-coherent glueing triple remains quasi-coherent
when `f` is quasi-compact and quasi-separated and `i` is of finite
presentation. -/
instance reverse_kernel_isQuasicoherent {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X) [IsClosedImmersion i]
    [QuasiCompact f] [QuasiSeparated f] [FinitePresentation i]
    (T : category f i) :
    (kernel (comparison f i T)).IsQuasicoherent :=
  sorry

/-- A morphism of glueing triples induces a morphism of reverse comparison
arrows that equalizes the target comparison. -/
theorem reverse_map_equalizes {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X) [IsClosedImmersion i] {T T' : category f i}
    (α : T ⟶ T') :
    (kernel.ι (comparison f i T) ≫
        biprod.map
          ((Modules.pushforward (closedImmersionComplementι i)).map α.fst.hom)
          ((Modules.pushforward f).map α.snd.hom)) ≫
      comparison f i T' = 0 :=
  sorry

/-- The underlying module morphism of `reverse` on a morphism of glueing
triples, as the induced map of kernels. -/
def reverse_map {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : Y ⟶ X)
    (i : Z ⟶ X) [IsClosedImmersion i] {T T' : category f i} (α : T ⟶ T') :
    kernel (comparison f i T) ⟶ kernel (comparison f i T') :=
  kernel.lift (comparison f i T')
    (kernel.ι (comparison f i T) ≫
      biprod.map
        ((Modules.pushforward (closedImmersionComplementι i)).map α.fst.hom)
        ((Modules.pushforward f).map α.snd.hom))
    (reverse_map_equalizes f i α)

/-- The reverse functor `QCoh(Y → X, Z) ⥤ QCoh X` sending a triple `(H, G, φ)`
to `kernel (j_* H ⊞ f_* G ⟶ (f ∘ j')_* (G|_V))`. -/
def reverse {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : Y ⟶ X) (i : Z ⟶ X)
    [IsClosedImmersion i] [QuasiCompact f] [QuasiSeparated f]
    [FinitePresentation i] :
    category f i ⥤ QCoh X where
  obj T := ⟨kernel (comparison f i T), reverse_kernel_isQuasicoherent f i T⟩
  map α := ObjectProperty.homMk (reverse_map f i α)
  map_id := sorry
  map_comp := sorry

/-- The underlying module of `reverse.obj T` is the kernel of `comparison`. -/
theorem reverse_obj {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : Y ⟶ X)
    (i : Z ⟶ X) [IsClosedImmersion i] [QuasiCompact f] [QuasiSeparated f]
    [FinitePresentation i] (T : category f i) :
    ((reverse f i).obj T).obj = kernel (comparison f i T) :=
  rfl

/-- The underlying module morphism of `reverse.map` is `reverse_map`. -/
theorem reverse_map_hom {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : Y ⟶ X)
    (i : Z ⟶ X) [IsClosedImmersion i] [QuasiCompact f] [QuasiSeparated f]
    [FinitePresentation i] {T T' : category f i} (α : T ⟶ T') :
    ((reverse f i).map α).hom = reverse_map f i α :=
  rfl

/-- The pairing of the pullback–pushforward units of `j` and `f` equalizes the
reverse comparison of `functor.obj F`. -/
theorem unit_equalizes {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : Y ⟶ X)
    (i : Z ⟶ X) [IsClosedImmersion i] [QuasiCompact f] [QuasiSeparated f]
    [FinitePresentation i] (F : QCoh X) :
    biprod.lift
        ((Modules.pullbackPushforwardAdjunction
            (closedImmersionComplementι i)).unit.app F.obj)
        ((Modules.pullbackPushforwardAdjunction f).unit.app F.obj) ≫
      comparison f i ((functor f i).obj F) = 0 :=
  sorry

/-- The underlying module morphism of the adjunction unit at `F`. -/
def unit_hom {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : Y ⟶ X) (i : Z ⟶ X)
    [IsClosedImmersion i] [QuasiCompact f] [QuasiSeparated f]
    [FinitePresentation i] (F : QCoh X) :
    F.obj ⟶ kernel (comparison f i ((functor f i).obj F)) :=
  kernel.lift (comparison f i ((functor f i).obj F))
    (biprod.lift
      ((Modules.pullbackPushforwardAdjunction
          (closedImmersionComplementι i)).unit.app F.obj)
      ((Modules.pullbackPushforwardAdjunction f).unit.app F.obj))
    (unit_equalizes f i F)

/-- The unit of `functor ⊣ reverse`, whose component at `F` is the map into the
reverse kernel induced by the units of `j^* ⊣ j_*` and `f^* ⊣ f_*`. -/
def unit {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : Y ⟶ X) (i : Z ⟶ X)
    [IsClosedImmersion i] [QuasiCompact f] [QuasiSeparated f]
    [FinitePresentation i] :
    𝟭 (QCoh X) ⟶ functor f i ⋙ reverse f i where
  app F := ObjectProperty.homMk (unit_hom f i F)
  naturality := sorry

/-- The underlying module morphism of `unit.app F` is `unit_hom`. -/
theorem unit_app {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : Y ⟶ X)
    (i : Z ⟶ X) [IsClosedImmersion i] [QuasiCompact f] [QuasiSeparated f]
    [FinitePresentation i] (F : QCoh X) :
    ((unit f i).app F).hom = unit_hom f i F :=
  rfl

/-- The first component of the adjunction counit at a glueing triple, as the
adjunct of `kernel.ι ≫ biprod.fst` under `j^* ⊣ j_*`. -/
def counit_fst {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : Y ⟶ X)
    (i : Z ⟶ X) [IsClosedImmersion i] [QuasiCompact f] [QuasiSeparated f]
    [FinitePresentation i] (T : category f i) :
    ((functor f i).obj ((reverse f i).obj T)).fst ⟶ T.fst :=
  ObjectProperty.homMk
    (((Modules.pullbackPushforwardAdjunction
            (closedImmersionComplementι i)).homEquiv
        ((reverse f i).obj T).obj T.fst.obj).symm
      (kernel.ι (comparison f i T) ≫ biprod.fst))

/-- The second component of the adjunction counit at a glueing triple, as the
adjunct of `kernel.ι ≫ biprod.snd` under `f^* ⊣ f_*`. -/
def counit_snd {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : Y ⟶ X)
    (i : Z ⟶ X) [IsClosedImmersion i] [QuasiCompact f] [QuasiSeparated f]
    [FinitePresentation i] (T : category f i) :
    ((functor f i).obj ((reverse f i).obj T)).snd ⟶ T.snd :=
  ObjectProperty.homMk
    (((Modules.pullbackPushforwardAdjunction f).homEquiv
        ((reverse f i).obj T).obj T.snd.obj).symm
      (kernel.ι (comparison f i T) ≫ biprod.snd))

/-- Compatibility of `counit_fst` and `counit_snd` with the glueing
isomorphisms. -/
theorem counit_w {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : Y ⟶ X)
    (i : Z ⟶ X) [IsClosedImmersion i] [QuasiCompact f] [QuasiSeparated f]
    [FinitePresentation i] (T : category f i) :
    (pullback (restrict f i)).map (counit_fst f i T) ≫ T.iso.hom =
      ((functor f i).obj ((reverse f i).obj T)).iso.hom ≫
        (pullback (closedImmersionComplementι (inverseImageι f i))).map
          (counit_snd f i T) :=
  sorry

/-- The component of the adjunction counit at a glueing triple. -/
def counit_app {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : Y ⟶ X)
    (i : Z ⟶ X) [IsClosedImmersion i] [QuasiCompact f] [QuasiSeparated f]
    [FinitePresentation i] (T : category f i) :
    (functor f i).obj ((reverse f i).obj T) ⟶ T where
  fst := counit_fst f i T
  snd := counit_snd f i T
  w := counit_w f i T

/-- The counit of `functor ⊣ reverse`, whose components are the adjuncts of the
kernel inclusions under `j^* ⊣ j_*` and `f^* ⊣ f_*`. -/
def counit {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : Y ⟶ X) (i : Z ⟶ X)
    [IsClosedImmersion i] [QuasiCompact f] [QuasiSeparated f]
    [FinitePresentation i] :
    reverse f i ⋙ functor f i ⟶ 𝟭 (category f i) where
  app := counit_app f i
  naturality := sorry

/-- The first component of `counit.app T` is `counit_fst`. -/
theorem counit_app_fst {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : Y ⟶ X)
    (i : Z ⟶ X) [IsClosedImmersion i] [QuasiCompact f] [QuasiSeparated f]
    [FinitePresentation i] (T : category f i) :
    ((counit f i).app T).fst = counit_fst f i T :=
  rfl

/-- The second component of `counit.app T` is `counit_snd`. -/
theorem counit_app_snd {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : Y ⟶ X)
    (i : Z ⟶ X) [IsClosedImmersion i] [QuasiCompact f] [QuasiSeparated f]
    [FinitePresentation i] (T : category f i) :
    ((counit f i).app T).snd = counit_snd f i T :=
  rfl

end AlgebraicGeometry.AlgebraicSpace.QCoh.FormalGlueing

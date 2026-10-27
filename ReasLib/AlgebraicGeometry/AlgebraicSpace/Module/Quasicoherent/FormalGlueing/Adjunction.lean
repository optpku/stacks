/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Quasicoherent.FormalGlueing
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Quasicoherent.Limits
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Quasicoherent.Pushforward
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FormalGlueing

/-!
# The reverse functor and adjunction for formal glueing

The kernel of the signed pushforward comparison of a quasi-coherent glueing
triple defines a right adjoint to the canonical glueing functor.
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
`restrictToComplement_comp`. -/
def fromH {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : Y ⟶ X) (i : Z ⟶ X)
    [IsClosedImmersion i] (T : category f i) :
    (Modules.pushforward (closedImmersionComplementι i)).obj T.fst.obj ⟶
      (Modules.pushforward
          (closedImmersionComplementι (inverseImageι f i) ≫ f)).obj
        ((Modules.pullback (closedImmersionComplementι (inverseImageι f i))).obj
          T.snd.obj) :=
  let j : closedImmersionComplement i ⟶ X := closedImmersionComplementι i
  let j' : closedImmersionComplement (inverseImageι f i) ⟶ Y :=
    closedImmersionComplementι (inverseImageι f i)
  let r : closedImmersionComplement (inverseImageι f i) ⟶
      closedImmersionComplement i := restrictToComplement f i
  let H : Modules (closedImmersionComplement i) := T.fst.obj
  let M : Modules (closedImmersionComplement (inverseImageι f i)) :=
    (Modules.pullback j').obj T.snd.obj
  let φ : (Modules.pullback r).obj H ⟶ M := T.iso.hom.hom
  let a : H ⟶ (Modules.pushforward r).obj M :=
    (Modules.pullbackPushforwardAdjunction r).unit.app H ≫
      (Modules.pushforward r).map φ
  let b : (Modules.pushforward j).obj H ⟶
      (Modules.pushforward j).obj ((Modules.pushforward r).obj M) :=
    (Modules.pushforward j).map a
  let c : (Modules.pushforward j).obj ((Modules.pushforward r).obj M) ⟶
      (Modules.pushforward (r ≫ j)).obj M :=
    (Modules.pushforwardComp r j).hom.app M
  let e : (Modules.pushforward (r ≫ j)).obj M ⟶
      (Modules.pushforward (j' ≫ f)).obj M :=
    eqToHom (congrArg
      (fun g : closedImmersionComplement (inverseImageι f i) ⟶ X ↦
        (Modules.pushforward g).obj M) (restrictToComplement_comp f i))
  b ≫ c ≫ e

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

/-- The induced map on reverse kernels preserves identity morphisms. -/
theorem reverse_map_id {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X) [IsClosedImmersion i] (T : category f i) :
    reverse_map f i (𝟙 T) = 𝟙 (kernel (comparison f i T)) :=
  sorry

/-- The induced map on reverse kernels preserves composition of morphisms. -/
theorem reverse_map_comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X) [IsClosedImmersion i]
    {T T' T'' : category f i} (α : T ⟶ T') (β : T' ⟶ T'') :
    reverse_map f i (α ≫ β) = reverse_map f i α ≫ reverse_map f i β :=
  sorry

/-- The reverse functor `QCoh(Y → X, Z) ⥤ QCoh X` sending a triple `(H, G, φ)`
to `kernel (j_* H ⊞ f_* G ⟶ (f ∘ j')_* (G|_V))`. -/
def reverse {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : Y ⟶ X) (i : Z ⟶ X)
    [IsClosedImmersion i] [QuasiCompact f] [QuasiSeparated f]
    [FinitePresentation i] :
    category f i ⥤ QCoh X where
  obj T := ⟨kernel (comparison f i T), reverse_kernel_isQuasicoherent f i T⟩
  map α := ObjectProperty.homMk (reverse_map f i α)
  map_id T := ObjectProperty.hom_ext (quasiCoherentModuleProperty X) (reverse_map_id f i T)
  map_comp α β :=
    ObjectProperty.hom_ext (quasiCoherentModuleProperty X) (reverse_map_comp f i α β)

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
    (pullback (restrictToComplement f i)).map (counit_fst f i T) ≫ T.iso.hom =
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

/-- The canonical kernel unit and projection counit satisfy the left triangle
identity on quasi-coherent modules. -/
theorem functor_reverse_left_triangle {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X)
    [QuasiCompact f] [QuasiSeparated f] [IsClosedImmersion i]
    [FinitePresentation i] [IsFormalGlueing f i] (F : QCoh X) :
    (functor f i).map ((unit f i).app F) ≫
      (counit f i).app ((functor f i).obj F) = 𝟙 ((functor f i).obj F) :=
  sorry

/-- The canonical kernel unit and projection counit satisfy the right triangle
identity on quasi-coherent glueing triples. -/
theorem functor_reverse_right_triangle {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X)
    [QuasiCompact f] [QuasiSeparated f] [IsClosedImmersion i]
    [FinitePresentation i] [IsFormalGlueing f i] (T : category f i) :
    (unit f i).app ((reverse f i).obj T) ≫
      (reverse f i).map ((counit f i).app T) = 𝟙 ((reverse f i).obj T) :=
  sorry

/-- The kernel of the signed pushforward comparison is right adjoint to the
canonical functor sending a quasi-coherent module to its glueing triple. -/
def functorReverseAdjunction {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X)
    [QuasiCompact f] [QuasiSeparated f] [IsClosedImmersion i]
    [FinitePresentation i] [IsFormalGlueing f i] :
    functor f i ⊣ reverse f i where
  unit := unit f i
  counit := counit f i
  left_triangle_components := functor_reverse_left_triangle f i
  right_triangle_components := functor_reverse_right_triangle f i

/-- The unit of `functorReverseAdjunction` is the reverse-kernel unit. -/
theorem functorReverseAdjunction_unit {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X)
    [QuasiCompact f] [QuasiSeparated f] [IsClosedImmersion i]
    [FinitePresentation i] [IsFormalGlueing f i] :
    (functorReverseAdjunction f i).unit = unit f i :=
  rfl

/-- The counit of `functorReverseAdjunction` is the reverse-kernel counit. -/
theorem functorReverseAdjunction_counit {S : Scheme.{u}}
    {X Y Z : AlgebraicSpace S} (f : Y ⟶ X) (i : Z ⟶ X)
    [QuasiCompact f] [QuasiSeparated f] [IsClosedImmersion i]
    [FinitePresentation i] [IsFormalGlueing f i] :
    (functorReverseAdjunction f i).counit = counit f i :=
  rfl

/-- The canonical glueing functor is a left adjoint, with right adjoint
`reverse`. -/
instance functor_isLeftAdjoint {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X)
    [QuasiCompact f] [QuasiSeparated f] [IsClosedImmersion i]
    [FinitePresentation i] [IsFormalGlueing f i] :
    (functor f i).IsLeftAdjoint :=
  ⟨reverse f i, ⟨functorReverseAdjunction f i⟩⟩

/-- The reverse functor is a right adjoint, with left adjoint `functor`. -/
instance reverse_isRightAdjoint {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X)
    [QuasiCompact f] [QuasiSeparated f] [IsClosedImmersion i]
    [FinitePresentation i] [IsFormalGlueing f i] :
    (reverse f i).IsRightAdjoint :=
  ⟨functor f i, ⟨functorReverseAdjunction f i⟩⟩
end AlgebraicGeometry.AlgebraicSpace.QCoh.FormalGlueing

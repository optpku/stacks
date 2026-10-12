/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Lemma_67_11_2_Pushforward
public import stacks_project.Chap78.Lemma_78_12_3_Pullback

/-!
# Pushforward of quasi-coherent modules on groupoids in algebraic spaces

Along a quasi-compact quasi-separated morphism of groupoids whose target square is cartesian
and whose target source and target maps are flat, equivariant quasi-coherent modules push
forward by `(F, α) ↦ (f_* F, f_* α)` on equivariant quasi-coherent modules.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits
open CategoryTheory.ObjectProperty

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

namespace QCoh

variable {S : Scheme.{u}} {B : AlgebraicSpace S}
variable {G H : GroupoidAlgebraicSpace B}

/-- The source square of a groupoid morphism is cartesian, obtained from the assumed target
square by inversion. -/
theorem sourceSquare_isPullback (f : Hom G H)
    (h_target : IsPullback f.arrow.left G.t.left H.t.left f.obj.left) :
    IsPullback f.arrow.left G.s.left H.s.left f.obj.left :=
  sorry

/-- Quasi-compactness of the object map of a groupoid morphism with cartesian target square
passes to the arrow map by base change. -/
theorem arrow_quasiCompact (f : Hom G H) [AlgebraicSpace.QuasiCompact f.obj.left]
    (h_target : IsPullback f.arrow.left G.t.left H.t.left f.obj.left) :
    AlgebraicSpace.QuasiCompact f.arrow.left :=
  sorry

/-- Quasi-separatedness of the object map of a groupoid morphism with cartesian target square
passes to the arrow map by base change. -/
theorem arrow_quasiSeparated (f : Hom G H) [AlgebraicSpace.QuasiSeparated f.obj.left]
    (h_target : IsPullback f.arrow.left G.t.left H.t.left f.obj.left) :
    AlgebraicSpace.QuasiSeparated f.arrow.left :=
  sorry

/-- Pushforward along the arrow component of a groupoid morphism with cartesian target square
preserves quasi-coherence. -/
theorem arrow_isQuasicoherent (f : Hom G H)
    [AlgebraicSpace.QuasiCompact f.obj.left] [AlgebraicSpace.QuasiSeparated f.obj.left]
    (h_target : IsPullback f.arrow.left G.t.left H.t.left f.obj.left)
    (F : AlgebraicSpace.QCoh G.R.left) :
    AlgebraicSpace.quasiCoherentModuleProperty H.R.left
      ((AlgebraicSpace.Modules.pushforward f.arrow.left).obj F.obj) :=
  sorry

/-- Quasi-coherent packaging of module pushforward along the arrow component. -/
def arrowPushforwardObj (f : Hom G H)
    [AlgebraicSpace.QuasiCompact f.obj.left] [AlgebraicSpace.QuasiSeparated f.obj.left]
    (h_target : IsPullback f.arrow.left G.t.left H.t.left f.obj.left)
    (F : AlgebraicSpace.QCoh G.R.left) : AlgebraicSpace.QCoh H.R.left :=
  ⟨(AlgebraicSpace.Modules.pushforward f.arrow.left).obj F.obj,
    arrow_isQuasicoherent f h_target F⟩

/-- Pushforward of a morphism along the arrow component, packaged on quasi-coherent modules. -/
def arrowPushforwardMap (f : Hom G H)
    [AlgebraicSpace.QuasiCompact f.obj.left] [AlgebraicSpace.QuasiSeparated f.obj.left]
    (h_target : IsPullback f.arrow.left G.t.left H.t.left f.obj.left)
    {M N : AlgebraicSpace.QCoh G.R.left} (a : M ⟶ N) :
    arrowPushforwardObj f h_target M ⟶ arrowPushforwardObj f h_target N :=
  (AlgebraicSpace.quasiCoherentModuleProperty H.R.left).homMk
    ((AlgebraicSpace.Modules.pushforward f.arrow.left).map a.hom)

/-- The underived base-change 2-cell `(t')^* f_* ⟶ f_* t^*` along the flipped target square. -/
def targetBaseChangeNatTrans (f : Hom G H)
    (h_target : IsPullback f.arrow.left G.t.left H.t.left f.obj.left) :
    AlgebraicSpace.Modules.pushforward f.obj.left ⋙
        AlgebraicSpace.Modules.pullback H.t.left ⟶
      AlgebraicSpace.Modules.pullback G.t.left ⋙
        AlgebraicSpace.Modules.pushforward f.arrow.left :=
  AlgebraicSpace.Modules.pushforwardBaseChangeNatTrans h_target.flip

/-- The underived mate component `(t')^* f_* F ⟶ f_* t^* F`. -/
def targetBaseChangeHom (f : Hom G H)
    [AlgebraicSpace.QuasiCompact f.obj.left] [AlgebraicSpace.QuasiSeparated f.obj.left]
    [AlgebraicSpace.Flat H.t.left]
    (h_target : IsPullback f.arrow.left G.t.left H.t.left f.obj.left)
    (F : AlgebraicSpace.QCoh G.U.left) :
    ((AlgebraicSpace.QCoh.pullback H.t.left).obj
        ((AlgebraicSpace.QCoh.pushforward f.obj.left).obj F)).obj ⟶
      (arrowPushforwardObj f h_target ((AlgebraicSpace.QCoh.pullback G.t.left).obj F)).obj :=
  (targetBaseChangeNatTrans f h_target).app F.obj

/-- The underived base-change component along the target square is an isomorphism on
quasi-coherent modules. -/
instance isIso_targetBaseChangeHom (f : Hom G H)
    [AlgebraicSpace.QuasiCompact f.obj.left] [AlgebraicSpace.QuasiSeparated f.obj.left]
    [AlgebraicSpace.Flat H.t.left]
    (h_target : IsPullback f.arrow.left G.t.left H.t.left f.obj.left)
    (F : AlgebraicSpace.QCoh G.U.left) :
    IsIso (targetBaseChangeHom f h_target F) :=
  sorry

/-- The identification `(t')^* f_* F ≅ f_* t^* F` obtained from the cartesian target square. -/
def targetBaseChangeIso (f : Hom G H)
    [AlgebraicSpace.QuasiCompact f.obj.left] [AlgebraicSpace.QuasiSeparated f.obj.left]
    [AlgebraicSpace.Flat H.t.left]
    (h_target : IsPullback f.arrow.left G.t.left H.t.left f.obj.left)
    (F : AlgebraicSpace.QCoh G.U.left) :
    (AlgebraicSpace.QCoh.pullback H.t.left).obj
        ((AlgebraicSpace.QCoh.pushforward f.obj.left).obj F) ≅
      arrowPushforwardObj f h_target ((AlgebraicSpace.QCoh.pullback G.t.left).obj F) :=
  (AlgebraicSpace.quasiCoherentModuleProperty H.R.left).isoMk
    (asIso (targetBaseChangeHom f h_target F))

/-- The forward component of `targetBaseChangeIso` is the mate of the flipped target square. -/
theorem targetBaseChangeIso_hom (f : Hom G H)
    [AlgebraicSpace.QuasiCompact f.obj.left] [AlgebraicSpace.QuasiSeparated f.obj.left]
    [AlgebraicSpace.Flat H.t.left]
    (h_target : IsPullback f.arrow.left G.t.left H.t.left f.obj.left)
    (F : AlgebraicSpace.QCoh G.U.left) :
    (targetBaseChangeIso f h_target F).hom.hom =
      (targetBaseChangeNatTrans f h_target).app F.obj :=
  sorry

/-- The cartesian identification of successive module pullbacks along the source square, using
the given commutativity `map_s_left f` rather than a cartesian witness. -/
def sourcePullbackCartesianIso (f : Hom G H) :
    AlgebraicSpace.Modules.pullback H.s.left ⋙
        AlgebraicSpace.Modules.pullback f.arrow.left ≅
      AlgebraicSpace.Modules.pullback f.obj.left ⋙
        AlgebraicSpace.Modules.pullback G.s.left :=
  AlgebraicSpace.Modules.pullbackCompIso f.arrow.left H.s.left ≪≫
    eqToIso (congrArg AlgebraicSpace.Modules.pullback (map_s_left f).symm) ≪≫
    (AlgebraicSpace.Modules.pullbackCompIso G.s.left f.obj.left).symm

/-- The underived base-change 2-cell `(s')^* f_* ⟶ f_* s^*` along the source square. -/
def sourceBaseChangeNatTrans (f : Hom G H) :
    AlgebraicSpace.Modules.pushforward f.obj.left ⋙
        AlgebraicSpace.Modules.pullback H.s.left ⟶
      AlgebraicSpace.Modules.pullback G.s.left ⋙
        AlgebraicSpace.Modules.pushforward f.arrow.left :=
  CategoryTheory.DerivedBaseChange.map
    (AlgebraicSpace.Modules.pullbackPushforwardAdjunction f.obj.left)
    (AlgebraicSpace.Modules.pullbackPushforwardAdjunction f.arrow.left)
    (sourcePullbackCartesianIso f)

/-- The underived mate component `(s')^* f_* F ⟶ f_* s^* F`. -/
def sourceBaseChangeHom (f : Hom G H)
    [AlgebraicSpace.QuasiCompact f.obj.left] [AlgebraicSpace.QuasiSeparated f.obj.left]
    [AlgebraicSpace.Flat H.s.left]
    (h_target : IsPullback f.arrow.left G.t.left H.t.left f.obj.left)
    (F : AlgebraicSpace.QCoh G.U.left) :
    ((AlgebraicSpace.QCoh.pullback H.s.left).obj
        ((AlgebraicSpace.QCoh.pushforward f.obj.left).obj F)).obj ⟶
      (arrowPushforwardObj f h_target ((AlgebraicSpace.QCoh.pullback G.s.left).obj F)).obj :=
  (sourceBaseChangeNatTrans f).app F.obj

/-- The underived base-change component along the source square is an isomorphism on
quasi-coherent modules; cartesianness of the source square is used only here. -/
instance isIso_sourceBaseChangeHom (f : Hom G H)
    [AlgebraicSpace.QuasiCompact f.obj.left] [AlgebraicSpace.QuasiSeparated f.obj.left]
    [AlgebraicSpace.Flat H.s.left]
    (h_target : IsPullback f.arrow.left G.t.left H.t.left f.obj.left)
    (F : AlgebraicSpace.QCoh G.U.left) :
    IsIso (sourceBaseChangeHom f h_target F) :=
  sorry

/-- The identification `(s')^* f_* F ≅ f_* s^* F` obtained from the source square. -/
def sourceBaseChangeIso (f : Hom G H)
    [AlgebraicSpace.QuasiCompact f.obj.left] [AlgebraicSpace.QuasiSeparated f.obj.left]
    [AlgebraicSpace.Flat H.s.left]
    (h_target : IsPullback f.arrow.left G.t.left H.t.left f.obj.left)
    (F : AlgebraicSpace.QCoh G.U.left) :
    (AlgebraicSpace.QCoh.pullback H.s.left).obj
        ((AlgebraicSpace.QCoh.pushforward f.obj.left).obj F) ≅
      arrowPushforwardObj f h_target ((AlgebraicSpace.QCoh.pullback G.s.left).obj F) :=
  (AlgebraicSpace.quasiCoherentModuleProperty H.R.left).isoMk
    (asIso (sourceBaseChangeHom f h_target F))

/-- The forward component of `sourceBaseChangeIso` is the source-square mate. -/
theorem sourceBaseChangeIso_hom (f : Hom G H)
    [AlgebraicSpace.QuasiCompact f.obj.left] [AlgebraicSpace.QuasiSeparated f.obj.left]
    [AlgebraicSpace.Flat H.s.left]
    (h_target : IsPullback f.arrow.left G.t.left H.t.left f.obj.left)
    (F : AlgebraicSpace.QCoh G.U.left) :
    (sourceBaseChangeIso f h_target F).hom.hom = (sourceBaseChangeNatTrans f).app F.obj :=
  sorry

/-- The pushed-forward equivariance map `f_* α`, transported across the source and target
base-change identifications. -/
def pushforwardAction (f : Hom G H)
    [AlgebraicSpace.QuasiCompact f.obj.left] [AlgebraicSpace.QuasiSeparated f.obj.left]
    [AlgebraicSpace.Flat H.s.left] [AlgebraicSpace.Flat H.t.left]
    (h_target : IsPullback f.arrow.left G.t.left H.t.left f.obj.left) (A : G.QCoh) :
    (AlgebraicSpace.QCoh.pullback H.t.left).obj
        ((AlgebraicSpace.QCoh.pushforward f.obj.left).obj A.obj) ⟶
      (AlgebraicSpace.QCoh.pullback H.s.left).obj
        ((AlgebraicSpace.QCoh.pushforward f.obj.left).obj A.obj) :=
  (targetBaseChangeIso f h_target A.obj).hom ≫
    arrowPushforwardMap f h_target A.action ≫
      (sourceBaseChangeIso f h_target A.obj).inv

/-- The pushed-forward equivariance map satisfies the cocycle law. -/
theorem pushforwardAction_cocycle (f : Hom G H)
    [AlgebraicSpace.QuasiCompact f.obj.left] [AlgebraicSpace.QuasiSeparated f.obj.left]
    [AlgebraicSpace.Flat H.s.left] [AlgebraicSpace.Flat H.t.left]
    (h_target : IsPullback f.arrow.left G.t.left H.t.left f.obj.left) (A : G.QCoh) :
    Cocycle H ((AlgebraicSpace.QCoh.pushforward f.obj.left).obj A.obj)
      (pushforwardAction f h_target A) :=
  sorry

/-- The pushed-forward equivariance map satisfies the unit law. -/
theorem pushforwardAction_unit (f : Hom G H)
    [AlgebraicSpace.QuasiCompact f.obj.left] [AlgebraicSpace.QuasiSeparated f.obj.left]
    [AlgebraicSpace.Flat H.s.left] [AlgebraicSpace.Flat H.t.left]
    (h_target : IsPullback f.arrow.left G.t.left H.t.left f.obj.left) (A : G.QCoh) :
    Unit H ((AlgebraicSpace.QCoh.pushforward f.obj.left).obj A.obj)
      (pushforwardAction f h_target A) :=
  sorry

/-- Pushforward of an equivariant quasi-coherent module along a morphism of groupoids. -/
def pushforwardObj (f : Hom G H)
    [AlgebraicSpace.QuasiCompact f.obj.left] [AlgebraicSpace.QuasiSeparated f.obj.left]
    [AlgebraicSpace.Flat H.s.left] [AlgebraicSpace.Flat H.t.left]
    (h_target : IsPullback f.arrow.left G.t.left H.t.left f.obj.left) (A : G.QCoh) : H.QCoh :=
  of ((AlgebraicSpace.QCoh.pushforward f.obj.left).obj A.obj) (pushforwardAction f h_target A)
    (pushforwardAction_cocycle f h_target A) (pushforwardAction_unit f h_target A)

/-- Pushforward of an underlying equivariant morphism remains compatible with equivariance. -/
theorem pushforwardMap_compatibility (f : Hom G H)
    [AlgebraicSpace.QuasiCompact f.obj.left] [AlgebraicSpace.QuasiSeparated f.obj.left]
    [AlgebraicSpace.Flat H.s.left] [AlgebraicSpace.Flat H.t.left]
    (h_target : IsPullback f.arrow.left G.t.left H.t.left f.obj.left)
    {M N : G.QCoh} (a : M ⟶ N) :
    (AlgebraicSpace.QCoh.pullback H.t.left).map
          ((AlgebraicSpace.QCoh.pushforward f.obj.left).map (hom a)) ≫
        (pushforwardObj f h_target N).action =
      (pushforwardObj f h_target M).action ≫
        (AlgebraicSpace.QCoh.pullback H.s.left).map
          ((AlgebraicSpace.QCoh.pushforward f.obj.left).map (hom a)) :=
  sorry

/-- Pushforward of a morphism of equivariant quasi-coherent modules. -/
def pushforwardMap (f : Hom G H)
    [AlgebraicSpace.QuasiCompact f.obj.left] [AlgebraicSpace.QuasiSeparated f.obj.left]
    [AlgebraicSpace.Flat H.s.left] [AlgebraicSpace.Flat H.t.left]
    (h_target : IsPullback f.arrow.left G.t.left H.t.left f.obj.left)
    {M N : G.QCoh} (a : M ⟶ N) : pushforwardObj f h_target M ⟶ pushforwardObj f h_target N :=
  System.Hom.of ((AlgebraicSpace.QCoh.pushforward f.obj.left).map (hom a))
    (pushforwardMap_compatibility f h_target a)

/-- Pushforward preserves identity equivariant morphisms. -/
theorem pushforwardMap_id (f : Hom G H)
    [AlgebraicSpace.QuasiCompact f.obj.left] [AlgebraicSpace.QuasiSeparated f.obj.left]
    [AlgebraicSpace.Flat H.s.left] [AlgebraicSpace.Flat H.t.left]
    (h_target : IsPullback f.arrow.left G.t.left H.t.left f.obj.left) (A : G.QCoh) :
    pushforwardMap f h_target (𝟙 A) = 𝟙 (pushforwardObj f h_target A) :=
  sorry

/-- Pushforward preserves composition of equivariant morphisms. -/
theorem pushforwardMap_comp (f : Hom G H)
    [AlgebraicSpace.QuasiCompact f.obj.left] [AlgebraicSpace.QuasiSeparated f.obj.left]
    [AlgebraicSpace.Flat H.s.left] [AlgebraicSpace.Flat H.t.left]
    (h_target : IsPullback f.arrow.left G.t.left H.t.left f.obj.left)
    {M N P : G.QCoh} (a : M ⟶ N) (b : N ⟶ P) :
    pushforwardMap f h_target (a ≫ b) =
      pushforwardMap f h_target a ≫ pushforwardMap f h_target b :=
  sorry

/-- Pushforward along a quasi-compact quasi-separated morphism of groupoids in algebraic spaces
with cartesian target square and flat source and target maps on the target groupoid. -/
def pushforward (f : Hom G H)
    [AlgebraicSpace.QuasiCompact f.obj.left] [AlgebraicSpace.QuasiSeparated f.obj.left]
    [AlgebraicSpace.Flat H.s.left] [AlgebraicSpace.Flat H.t.left]
    (h_target : IsPullback f.arrow.left G.t.left H.t.left f.obj.left) : G.QCoh ⥤ H.QCoh where
  obj := pushforwardObj f h_target
  map := pushforwardMap f h_target
  map_id := pushforwardMap_id f h_target
  map_comp := pushforwardMap_comp f h_target

/-- The underlying module of a pushed-forward equivariant object is ordinary qcqs pushforward
along the object component. -/
theorem pushforward_obj (f : Hom G H)
    [AlgebraicSpace.QuasiCompact f.obj.left] [AlgebraicSpace.QuasiSeparated f.obj.left]
    [AlgebraicSpace.Flat H.s.left] [AlgebraicSpace.Flat H.t.left]
    (h_target : IsPullback f.arrow.left G.t.left H.t.left f.obj.left) (A : G.QCoh) :
    ((pushforward f h_target).obj A).obj =
      (AlgebraicSpace.QCoh.pushforward f.obj.left).obj A.obj :=
  sorry

/-- The equivariance map of a pushed-forward object is the transported pushforward of the
original action. -/
theorem pushforward_action (f : Hom G H)
    [AlgebraicSpace.QuasiCompact f.obj.left] [AlgebraicSpace.QuasiSeparated f.obj.left]
    [AlgebraicSpace.Flat H.s.left] [AlgebraicSpace.Flat H.t.left]
    (h_target : IsPullback f.arrow.left G.t.left H.t.left f.obj.left) (A : G.QCoh) :
    ((pushforward f h_target).obj A).action = pushforwardAction f h_target A :=
  sorry

/-- The underlying map of a pushed-forward equivariant morphism is ordinary qcqs pushforward
along the object component. -/
theorem pushforward_map (f : Hom G H)
    [AlgebraicSpace.QuasiCompact f.obj.left] [AlgebraicSpace.QuasiSeparated f.obj.left]
    [AlgebraicSpace.Flat H.s.left] [AlgebraicSpace.Flat H.t.left]
    (h_target : IsPullback f.arrow.left G.t.left H.t.left f.obj.left)
    {M N : G.QCoh} (a : M ⟶ N) :
    hom ((pushforward f h_target).map a) =
      (AlgebraicSpace.QCoh.pushforward f.obj.left).map (hom a) :=
  sorry

end QCoh

end AlgebraicGeometry.GroupoidAlgebraicSpace

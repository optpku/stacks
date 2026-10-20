/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.MayerVietoris.Pushforward
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.EtaleBaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Pushforward.Shift
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.MayerVietoris
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived.Homotopy.Exact

/-! Relative Mayer–Vietoris triangles for derived module pushforward. -/

@[expose] public section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules CategoryTheory.Limits
open CategoryTheory.Functor CategoryTheory.Pretriangulated ComplexShape
open AlgebraicGeometry.AlgebraicSpace.SmallEtaleModuleGlueing (restrictFunctorComp)
noncomputable section
universe u
namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}}

/-- Restriction to `U` followed by pushforward along `a = j ≫ f`. -/
abbrev along {U X Y : AlgebraicSpace S} (f : X ⟶ Y) (j : U ⟶ X) [Etale j] :
    X.Modules ⥤ Y.Modules :=
  restrictFunctor j ⋙ pushforward (j ≫ f)

/-- `along f j` is restriction along `j` followed by pushforward along `j ≫ f`. -/
theorem along_eq {U X Y : AlgebraicSpace S} (f : X ⟶ Y) (j : U ⟶ X) [Etale j] :
    along f j = restrictFunctor j ⋙ pushforward (j ≫ f) :=
  rfl

/-- The underived comparison `f_* ⟶ a_* ((-)|_U)` obtained from the étale unit of `j`
and `pushforwardComp j f`. -/
def alongUnit {U X Y : AlgebraicSpace S} (f : X ⟶ Y) (j : U ⟶ X) [Etale j] :
    pushforward f ⟶ along f j where
  app F :=
    (pushforward f).map ((restrictAdjunction j).unit.app F) ≫
      (pushforwardComp j f).hom.app (restrict F j)
  naturality := fun _ _ _ ↦ sorry

/-- `alongUnit` is pushforward of the étale unit of `j`, followed by `pushforwardComp`. -/
theorem alongUnit_eq {U X Y : AlgebraicSpace S} (f : X ⟶ Y) (j : U ⟶ X) [Etale j]
    (F : X.Modules) :
    (alongUnit f j).app F =
      (pushforward f).map ((restrictAdjunction j).unit.app F) ≫
        (pushforwardComp j f).hom.app (restrict F j) :=
  rfl

-- The private transport proof occurs in the concrete public restriction map;
-- enable export elaboration here and at its use without publishing the name.
set_option backward.privateInPublic true in
/-- Transport `along f p` along an equality of étale morphisms to `X`. -/
private theorem alongObj_eq {W X Y : AlgebraicSpace S} {p q : W ⟶ X} [hp : Etale p] [hq : Etale q]
    (h : p = q) (f : X ⟶ Y) (F : X.Modules) :
    (along f p).obj F = (along f q).obj F :=
  Eq.rec (motive := fun r (_ : p = r) =>
      ∀ hr : Etale r,
        (@along S W X Y f p hp).obj F = (@along S W X Y f r hr).obj F)
    (fun hr =>
      congrArg (fun inst : Etale p => (@along S W X Y f p inst).obj F)
        (Subsingleton.elim hp hr))
    h hq

/-- The underived overlap comparison `a_* ((-)|_U) ⟶ a_W_* ((-)|_W)` along an étale
factorization `p : W ⟶ U`. -/
def alongRestriction {W U X Y : AlgebraicSpace S} (f : X ⟶ Y) (j : U ⟶ X) [Etale j]
    (p : W ⟶ U) [Etale p] :
    along f j ⟶ along f (p ≫ j) where
  app F :=
    (pushforward (j ≫ f)).map ((restrictAdjunction p).unit.app (restrict F j)) ≫
      (pushforwardComp p (j ≫ f)).hom.app ((restrictFunctor p).obj (restrict F j)) ≫
        (pushforward (p ≫ (j ≫ f))).map ((restrictFunctorComp p j).hom.app F) ≫
          eqToHom
            (congrArg (fun q => (pushforward q).obj ((restrictFunctor (p ≫ j)).obj F))
              (Category.assoc p j f).symm)
  naturality := fun _ _ _ ↦ sorry

/-- `alongRestriction` is the unit of `p` followed by `pushforwardComp p (j ≫ f)`. -/
theorem alongRestriction_eq {W U X Y : AlgebraicSpace S} (f : X ⟶ Y) (j : U ⟶ X)
    [Etale j] (p : W ⟶ U) [Etale p] (F : X.Modules) :
    (alongRestriction f j p).app F =
      (pushforward (j ≫ f)).map ((restrictAdjunction p).unit.app (restrict F j)) ≫
        (pushforwardComp p (j ≫ f)).hom.app ((restrictFunctor p).obj (restrict F j)) ≫
          (pushforward (p ≫ (j ≫ f))).map ((restrictFunctorComp p j).hom.app F) ≫
            eqToHom
              (congrArg (fun q => (pushforward q).obj ((restrictFunctor (p ≫ j)).obj F))
                (Category.assoc p j f).symm) :=
  rfl

/-- On a K-injective complex, `f_*` computes `Rf_*`. -/
instance isIso_mayerVietorisRelativePushforward_unit_app
    {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (K : CochainComplex X.Modules ℤ) [K.IsKInjective] :
    IsIso ((Functor.RightDerived.KInjective.unit.{u} (pushforward f)).app K) :=
  sorry

variable {U V X Y : AlgebraicSpace S} (f : X ⟶ Y) (j : U ⟶ X) [Etale j]
  (g : V ⟶ X) [Etale g]

set_option backward.privateInPublic true in
/-- The `V`-leg overlap restriction of `along`, transported along `fiberHom_eq`. -/
def alongRestriction_fiberHom :
    along f g ⟶ along f (fiberHom j g) where
  app F :=
    (alongRestriction f g (Limits.pullback.snd j g)).app F ≫
      eqToHom (alongObj_eq (fiberHom_eq j g).symm f F)
  naturality := fun _ _ _ ↦ sorry

/-- Derived `U`-leg unit `Rf_* E ⟶ Ra_*(E|_U)`. -/
def mayerVietorisRelativePushforwardιU (E : ModuleDerived X) :
    (moduleDerivedPushforward f).obj E ⟶
      (moduleDerivedPushforward (j ≫ f)).obj ((restrictFunctorDerived j).obj E) :=
  (Functor.RightDerived.Homotopy.mapNatTrans (alongUnit f j)).app E ≫
    (asIso (derivedRestrictPushforwardComparison (h := j) (f' := j ≫ f))).hom.app E

/-- Derived `V`-leg unit `Rf_* E ⟶ Rb_*(E|_V)`. -/
def mayerVietorisRelativePushforwardιV (E : ModuleDerived X) :
    (moduleDerivedPushforward f).obj E ⟶
      (moduleDerivedPushforward (g ≫ f)).obj ((restrictFunctorDerived g).obj E) :=
  (Functor.RightDerived.Homotopy.mapNatTrans (alongUnit f g)).app E ≫
    (asIso (derivedRestrictPushforwardComparison (h := g) (f' := g ≫ f))).hom.app E

/-- The first relative Mayer–Vietoris arrow
`Rf_* E ⟶ Ra_*(E|_U) ⊞ Rb_*(E|_V)`. -/
def mayerVietorisRelativePushforwardι (E : ModuleDerived X) :
    (moduleDerivedPushforward f).obj E ⟶
      biprod ((moduleDerivedPushforward (j ≫ f)).obj ((restrictFunctorDerived j).obj E))
        ((moduleDerivedPushforward (g ≫ f)).obj ((restrictFunctorDerived g).obj E)) :=
  biprod.lift (mayerVietorisRelativePushforwardιU f j E)
    (mayerVietorisRelativePushforwardιV f g E)

/-- Derived `U`-leg overlap restriction `Ra_*(E|_U) ⟶ Rc_*(E|_W)`. -/
def mayerVietorisRelativePushforwardπU (E : ModuleDerived X) :
    (moduleDerivedPushforward (j ≫ f)).obj ((restrictFunctorDerived j).obj E) ⟶
      (moduleDerivedPushforward (fiberHom j g ≫ f)).obj
        ((restrictFunctorDerived (fiberHom j g)).obj E) :=
  (asIso (derivedRestrictPushforwardComparison (h := j) (f' := j ≫ f))).inv.app E ≫
    (Functor.RightDerived.Homotopy.mapNatTrans
      (alongRestriction f j (Limits.pullback.fst j g))).app E ≫
    (asIso (derivedRestrictPushforwardComparison (h := fiberHom j g) (f' := fiberHom j g ≫ f))).hom.app E

/-- Derived `V`-leg overlap restriction `Rb_*(E|_V) ⟶ Rc_*(E|_W)`. -/
def mayerVietorisRelativePushforwardπV (E : ModuleDerived X) :
    (moduleDerivedPushforward (g ≫ f)).obj ((restrictFunctorDerived g).obj E) ⟶
      (moduleDerivedPushforward (fiberHom j g ≫ f)).obj
        ((restrictFunctorDerived (fiberHom j g)).obj E) :=
  (asIso (derivedRestrictPushforwardComparison (h := g) (f' := g ≫ f))).inv.app E ≫
    (Functor.RightDerived.Homotopy.mapNatTrans
      (alongRestriction_fiberHom f j g)).app E ≫
    (asIso (derivedRestrictPushforwardComparison (h := fiberHom j g) (f' := fiberHom j g ≫ f))).hom.app E

/-- The second relative Mayer–Vietoris arrow
`Ra_*(E|_U) ⊞ Rb_*(E|_V) ⟶ Rc_*(E|_W)`, with a sign on the `V`-leg. -/
def mayerVietorisRelativePushforwardπ (E : ModuleDerived X) :
    biprod ((moduleDerivedPushforward (j ≫ f)).obj ((restrictFunctorDerived j).obj E))
        ((moduleDerivedPushforward (g ≫ f)).obj ((restrictFunctorDerived g).obj E)) ⟶
      (moduleDerivedPushforward (fiberHom j g ≫ f)).obj
        ((restrictFunctorDerived (fiberHom j g)).obj E) :=
  biprod.desc (mayerVietorisRelativePushforwardπU f j g E)
    (-mayerVietorisRelativePushforwardπV f j g E)

/-- The cochain-level first relative Mayer–Vietoris arrow. -/
def mayerVietorisRelativePushforwardCochainι (K : CochainComplex X.Modules ℤ) :
    ((pushforward f).mapHomologicalComplex (up ℤ)).obj K ⟶
      biprod (((along f j).mapHomologicalComplex (up ℤ)).obj K)
        (((along f g).mapHomologicalComplex (up ℤ)).obj K) :=
  biprod.lift
    ((NatTrans.mapHomologicalComplex (alongUnit f j) (up ℤ)).app K)
    ((NatTrans.mapHomologicalComplex (alongUnit f g) (up ℤ)).app K)

/-- The cochain-level second relative Mayer–Vietoris arrow. -/
def mayerVietorisRelativePushforwardCochainπ (K : CochainComplex X.Modules ℤ) :
    biprod (((along f j).mapHomologicalComplex (up ℤ)).obj K)
        (((along f g).mapHomologicalComplex (up ℤ)).obj K) ⟶
      ((along f (fiberHom j g)).mapHomologicalComplex (up ℤ)).obj K :=
  biprod.desc
    ((NatTrans.mapHomologicalComplex
      (alongRestriction f j (Limits.pullback.fst j g)) (up ℤ)).app K)
    (-(NatTrans.mapHomologicalComplex (alongRestriction_fiberHom f j g) (up ℤ)).app K)

/-- The short complex of cochain complexes obtained by applying the module-level
relative Mayer–Vietoris arrows degreewise. -/
def mayerVietorisRelativePushforwardCochainShortComplex
    (K : CochainComplex X.Modules ℤ) :
    ShortComplex (CochainComplex Y.Modules ℤ) :=
  ShortComplex.mk (mayerVietorisRelativePushforwardCochainι f j g K)
    (mayerVietorisRelativePushforwardCochainπ f j g K) sorry

variable [IsElementaryDistinguishedSquare j g]

/-- The cochain-level relative Mayer–Vietoris sequence is short exact on complexes
with injective terms, using `R¹ f_* I = 0`. -/
theorem mayerVietorisRelativePushforwardCochain_shortExact
    (K : CochainComplex X.Modules ℤ) [∀ n, Injective (K.X n)] :
    (mayerVietorisRelativePushforwardCochainShortComplex f j g K).ShortExact :=
  sorry

/-- Cochain-level connecting map of the relative Mayer–Vietoris short exact sequence on a
complex with injective terms. -/
def mayerVietorisRelativePushforwardδCochain
    (K : CochainComplex X.Modules ℤ) [∀ n, Injective (K.X n)] :
    DerivedCategory.Q.obj
        (((along f (fiberHom j g)).mapHomologicalComplex (up ℤ)).obj K) ⟶
      DerivedCategory.Q.obj
          (((pushforward f).mapHomologicalComplex (up ℤ)).obj K)⟦(1 : ℤ)⟧ :=
  DerivedCategory.triangleOfSESδ
    (mayerVietorisRelativePushforwardCochain_shortExact f j g K)

/-- On a K-injective termwise-injective complex, the cochain connecting map lands in `Rf_*`
after the K-injective unit. -/
def mayerVietorisRelativePushforwardδCochain_kInjective
    (K : CochainComplex X.Modules ℤ) [K.IsKInjective] [∀ n, Injective (K.X n)] :
    DerivedCategory.Q.obj
        (((along f (fiberHom j g)).mapHomologicalComplex (up ℤ)).obj K) ⟶
      ((moduleDerivedPushforward f).obj (DerivedCategory.Q.obj K))⟦(1 : ℤ)⟧ :=
  mayerVietorisRelativePushforwardδCochain f j g K ≫
    ((Functor.RightDerived.KInjective.unit.{u} (pushforward f)).app K)⟦(1 : ℤ)⟧'

-- The private composition isomorphism occurs in the concrete public connecting map;
-- enable export elaboration here and at its use without publishing the name.
set_option backward.privateInPublic true in
/-- Underived identification of restriction-then-étale-pushforward followed by `f_*`
with `along f (fiberHom j g)`. -/
private def alongCompIso :
    (restrictFunctor (fiberHom j g) ⋙ pushforward (fiberHom j g)) ⋙ pushforward f ≅
      along f (fiberHom j g) :=
  Functor.associator (restrictFunctor (fiberHom j g))
      (pushforward (fiberHom j g)) (pushforward f) ≪≫
    isoWhiskerLeft (restrictFunctor (fiberHom j g)) (pushforwardComp (fiberHom j g) f)

/-- `alongCompIso` is the associator of `restrictFunctor` followed by `pushforwardComp`. -/
private theorem alongCompIso_eq :
    alongCompIso f j g =
      Functor.associator (restrictFunctor (fiberHom j g))
          (pushforward (fiberHom j g)) (pushforward f) ≪≫
        isoWhiskerLeft (restrictFunctor (fiberHom j g))
          (pushforwardComp (fiberHom j g) f) :=
  rfl

set_option backward.privateInPublic true in
/-- Cochain-level connecting maps into `Rf_* ((-)⟦1⟧)`, obtained from the identity-base
Mayer–Vietoris `triangleOfSESδ` and `pushforwardComp`. This NatTrans is the
`rightDerivedDesc` input; it agrees with `δCochain` after the K-injective unit on
termwise-injective K-injective complexes. -/
def mayerVietorisRelativePushforwardδCochainNatTrans :
    (along f (fiberHom j g)).mapHomologicalComplex (up ℤ) ⋙
        (DerivedCategory.Q : CochainComplex Y.Modules ℤ ⥤ ModuleDerived Y) ⟶
      (DerivedCategory.Q : CochainComplex X.Modules ℤ ⥤ ModuleDerived X) ⋙
        shiftFunctor (ModuleDerived X) (1 : ℤ) ⋙ moduleDerivedPushforward f where
  app K :=
    DerivedCategory.Q.map
        ((Functor.mapHomologicalComplexCompIso (alongCompIso f j g) (up ℤ)).inv.app K) ≫
      (Functor.RightDerived.KInjective.unit.{u} (pushforward f)).app
        (((restrictFunctor (fiberHom j g) ⋙
            pushforward (fiberHom j g)).mapHomologicalComplex (up ℤ)).obj K) ≫
      (moduleDerivedPushforward f).map ((mayerVietorisPushforwardδCochain j g).app K)
  naturality := fun _ _ _ ↦ sorry

/-- Connecting morphism of derived functors, obtained by descending the cochain-level
connecting NatTrans along the K-injective unit of the overlap composite. -/
def mayerVietorisRelativePushforwardδNatTrans :
    Functor.RightDerived.Homotopy.functor (along f (fiberHom j g)) ⟶
      shiftFunctor (ModuleDerived X) (1 : ℤ) ⋙ moduleDerivedPushforward f :=
  Functor.RightDerived.Homotopy.cochainExtensionDesc
    (along f (fiberHom j g))
    (shiftFunctor (ModuleDerived X) (1 : ℤ) ⋙ moduleDerivedPushforward f)
    (mayerVietorisRelativePushforwardδCochainNatTrans f j g)

/-- On a K-injective termwise-injective complex, the descended connecting map agrees with
`triangleOfSESδ` of the guarded relative short exact sequence after the K-injective unit. -/
theorem mayerVietorisRelativePushforwardδCochain_kInjective_eq
    (K : CochainComplex X.Modules ℤ) [K.IsKInjective] [∀ n, Injective (K.X n)] :
    mayerVietorisRelativePushforwardδCochain_kInjective f j g K =
      (mayerVietorisRelativePushforwardδCochainNatTrans f j g).app K ≫
        (moduleDerivedPushforward_commShiftIso1 f).hom.app (DerivedCategory.Q.obj K) :=
  sorry

/-- The connecting morphism of the relative Mayer–Vietoris triangle in `D(𝒪_Y)`. -/
def mayerVietorisRelativePushforwardδ (E : ModuleDerived X) :
    (moduleDerivedPushforward (fiberHom j g ≫ f)).obj
      ((restrictFunctorDerived (fiberHom j g)).obj E) ⟶
      ((moduleDerivedPushforward f).obj E)⟦(1 : ℤ)⟧ :=
  (asIso (derivedRestrictPushforwardComparison (h := fiberHom j g) (f' := fiberHom j g ≫ f))).inv.app E ≫
    (mayerVietorisRelativePushforwardδNatTrans f j g).app E ≫
    (moduleDerivedPushforward_commShiftIso1 f).hom.app E

/-- The relative Mayer–Vietoris distinguished-triangle data of derived pushforward in
`D(𝒪_Y)`. -/
def mayerVietorisRelativePushforwardTriangle (E : ModuleDerived X) :
    Triangle (ModuleDerived Y) :=
  Triangle.mk (mayerVietorisRelativePushforwardι f j g E)
    (mayerVietorisRelativePushforwardπ f j g E)
    (mayerVietorisRelativePushforwardδ f j g E)

/-- The first vertex of the relative Mayer–Vietoris triangle is `Rf_* E`. -/
theorem mayerVietorisRelativePushforwardTriangle_obj₁ (E : ModuleDerived X) :
    (mayerVietorisRelativePushforwardTriangle f j g E).obj₁ =
      (moduleDerivedPushforward f).obj E :=
  rfl

/-- The second vertex of the relative Mayer–Vietoris triangle is
`Ra_*(E|_U) ⊞ Rb_*(E|_V)`. -/
theorem mayerVietorisRelativePushforwardTriangle_obj₂ (E : ModuleDerived X) :
    (mayerVietorisRelativePushforwardTriangle f j g E).obj₂ =
      biprod ((moduleDerivedPushforward (j ≫ f)).obj ((restrictFunctorDerived j).obj E))
        ((moduleDerivedPushforward (g ≫ f)).obj ((restrictFunctorDerived g).obj E)) :=
  rfl

/-- The third vertex of the relative Mayer–Vietoris triangle is `Rc_*(E|_{U ×_X V})`. -/
theorem mayerVietorisRelativePushforwardTriangle_obj₃ (E : ModuleDerived X) :
    (mayerVietorisRelativePushforwardTriangle f j g E).obj₃ =
      (moduleDerivedPushforward (fiberHom j g ≫ f)).obj
        ((restrictFunctorDerived (fiberHom j g)).obj E) :=
  rfl

/-- The relative Mayer–Vietoris triangle as a functor of `E` in `D(𝒪_X)`. -/
def mayerVietorisRelativePushforwardTriangleFunctor :
    ModuleDerived X ⥤ Triangle (ModuleDerived Y) where
  obj E := mayerVietorisRelativePushforwardTriangle f j g E
  map {E E'} φ :=
    Triangle.homMk (mayerVietorisRelativePushforwardTriangle f j g E)
      (mayerVietorisRelativePushforwardTriangle f j g E')
      ((moduleDerivedPushforward f).map φ)
      (biprod.map
        ((moduleDerivedPushforward (j ≫ f)).map ((restrictFunctorDerived j).map φ))
        ((moduleDerivedPushforward (g ≫ f)).map ((restrictFunctorDerived g).map φ)))
      ((moduleDerivedPushforward (fiberHom j g ≫ f)).map
        ((restrictFunctorDerived (fiberHom j g)).map φ))
      sorry sorry sorry
  map_id := sorry
  map_comp := sorry

/-- The triangle functor evaluates at `E` as `mayerVietorisRelativePushforwardTriangle`. -/
theorem mayerVietorisRelativePushforwardTriangleFunctor_obj (E : ModuleDerived X) :
    (mayerVietorisRelativePushforwardTriangleFunctor f j g).obj E =
      mayerVietorisRelativePushforwardTriangle f j g E :=
  rfl


/-- The relative Mayer–Vietoris triangle is distinguished. -/
theorem mayerVietorisRelativePushforward_mem_distTriang {S : Scheme.{u}}
    {U V X Y : AlgebraicSpace S} (f : X ⟶ Y) (j : U ⟶ X) [Etale j] (g : V ⟶ X)
    [Etale g] [IsElementaryDistinguishedSquare j g] (E : ModuleDerived X) :
    mayerVietorisRelativePushforwardTriangle f j g E ∈ distTriang (ModuleDerived Y) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules


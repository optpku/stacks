module

public import Mathlib.AlgebraicGeometry.Limits
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.Pullback

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Bicategory

universe u v

namespace AlgebraicGeometry.Scheme.QCoh.GaloisDescent

variable {G : Type v} [Group G] {X Y : Scheme.{u}} (p : X ⟶ Y)
variable (rho : Gᵐᵒᵖ →* Aut (Over.mk p : Over Y))

/-- The automorphism of `X` indexed by `sigma`, obtained from an opposite-group action over
`Y`. -/
def actionHom (sigma : G) : X ⟶ X :=
  (rho (MulOpposite.op sigma)).hom.left

/-- Every `actionHom p rho sigma` lies over `Y`. -/
theorem actionHom_over (sigma : G) : actionHom p rho sigma ≫ p = p := sorry

/-- The identity element acts by the identity morphism. -/
theorem actionHom_one : actionHom p rho 1 = 𝟙 X := sorry

/-- The opposite-group convention makes multiplication correspond to categorical
composition in the order used by pullback. -/
theorem actionHom_mul (sigma tau : G) :
    actionHom p rho (sigma * tau) = actionHom p rho sigma ≫ actionHom p rho tau := sorry

/-- The compatibility needed to lift the `sigma`-th graph into `pullback p p`. -/
theorem orbitLift_fac (sigma : G) :
    𝟙 X ≫ p = actionHom p rho sigma ≫ p := sorry

/-- The orbit map `G × X ⟶ X ×_Y X`, with `G × X` represented by the
finite coproduct of copies of `X`. -/
noncomputable def orbitMap [Finite G] :
    (∐ fun _ : G ↦ X) ⟶ CategoryTheory.Limits.pullback p p :=
  Sigma.desc fun sigma ↦
    CategoryTheory.Limits.pullback.lift
      (𝟙 X) (actionHom p rho sigma) (orbitLift_fac p rho sigma)

/-- On the `sigma`-th coproduct summand, `orbitMap` is the graph of
`actionHom p rho sigma`. -/
theorem orbitMap_ι [Finite G] (sigma : G) :
    Sigma.ι (fun _ : G ↦ X) sigma ≫ orbitMap p rho =
      CategoryTheory.Limits.pullback.lift
        (𝟙 X) (actionHom p rho sigma) (orbitLift_fac p rho sigma) := sorry

/-- Pullback first by `actionHom p rho tau` and then by `actionHom p rho sigma` agrees,
up to the canonical comparison, with pullback by `actionHom p rho (sigma * tau)`. -/
noncomputable def pullbackMulIso (sigma tau : G) :
    QCoh.pullback (actionHom p rho tau) ⋙ QCoh.pullback (actionHom p rho sigma) ≅
      QCoh.pullback (actionHom p rho (sigma * tau)) :=
  (Cat.Hom.toNatIso
    ((QCoh.pseudofunctor.map₂Iso
      (eqToIso
        (congrArg (fun f : X ⟶ X ↦ f.op.toLoc)
          (actionHom_mul p rho sigma tau)))).trans
      (QCoh.pseudofunctor.mapComp
        (actionHom p rho tau).op.toLoc (actionHom p rho sigma).op.toLoc))).symm

/-- A quasi-coherent module on `X` equipped with pullback-twisted `G`-equivariance. -/
structure System where
  /-- The underlying quasi-coherent module. -/
  obj : QCoh X
  /-- The isomorphism from the underlying module to its pullback by `sigma`. -/
  iso (sigma : G) : obj ≅ (QCoh.pullback (actionHom p rho sigma)).obj obj
  /-- The transported cocycle equation for the pullback-twisted isomorphisms. -/
  cocycle (sigma tau : G) :
    (iso (sigma * tau)).hom =
      (iso sigma).hom ≫
        (QCoh.pullback (actionHom p rho sigma)).map (iso tau).hom ≫
          (pullbackMulIso p rho sigma tau).hom.app obj

namespace System

/-- Construct an equivariant system from its module, isomorphisms, and cocycle. -/
def of (F : QCoh X)
    (phi : ∀ sigma : G, F ≅ (QCoh.pullback (actionHom p rho sigma)).obj F)
    (hphi : ∀ sigma tau : G,
      (phi (sigma * tau)).hom =
        (phi sigma).hom ≫
          (QCoh.pullback (actionHom p rho sigma)).map (phi tau).hom ≫
            (pullbackMulIso p rho sigma tau).hom.app F) : System p rho where
  obj := F
  iso := phi
  cocycle := hphi

/-- `System.of` retains the supplied quasi-coherent module. -/
theorem of_obj (F : QCoh X)
    (phi : ∀ sigma : G, F ≅ (QCoh.pullback (actionHom p rho sigma)).obj F)
    (hphi : ∀ sigma tau : G,
      (phi (sigma * tau)).hom =
        (phi sigma).hom ≫
          (QCoh.pullback (actionHom p rho sigma)).map (phi tau).hom ≫
            (pullbackMulIso p rho sigma tau).hom.app F) :
    (of p rho F phi hphi).obj = F := sorry

/-- `System.of` retains each supplied equivariance isomorphism. -/
theorem of_iso (F : QCoh X)
    (phi : ∀ sigma : G, F ≅ (QCoh.pullback (actionHom p rho sigma)).obj F)
    (hphi : ∀ sigma tau : G,
      (phi (sigma * tau)).hom =
        (phi sigma).hom ≫
          (QCoh.pullback (actionHom p rho sigma)).map (phi tau).hom ≫
            (pullbackMulIso p rho sigma tau).hom.app F) (sigma : G) :
    (of p rho F phi hphi).iso sigma = phi sigma := sorry

/-- A morphism of equivariant systems is a quasi-coherent-module morphism commuting with every
equivariance isomorphism. -/
structure Hom (D E : System p rho) where
  /-- The underlying morphism of quasi-coherent modules. -/
  hom : D.obj ⟶ E.obj
  /-- Compatibility with the equivariance isomorphism indexed by `sigma`. -/
  compatibility (sigma : G) :
    (D.iso sigma).hom ≫ (QCoh.pullback (actionHom p rho sigma)).map hom =
      hom ≫ (E.iso sigma).hom

namespace Hom

variable {D E K L : System p rho}

/-- Construct an equivariant morphism from its underlying map and compatibility equation. -/
def of (f : D.obj ⟶ E.obj)
    (hf : ∀ sigma : G,
      (D.iso sigma).hom ≫ (QCoh.pullback (actionHom p rho sigma)).map f =
        f ≫ (E.iso sigma).hom) : Hom p rho D E where
  hom := f
  compatibility := hf

/-- Two equivariant morphisms are equal when their underlying maps are equal. -/
theorem ext {f g : Hom p rho D E} (h : f.hom = g.hom) : f = g := sorry

/-- The identity map satisfies the equivariance compatibility equation. -/
theorem id_compatibility (D : System p rho) (sigma : G) :
    (D.iso sigma).hom ≫
        (QCoh.pullback (actionHom p rho sigma)).map (𝟙 D.obj) =
      𝟙 D.obj ≫ (D.iso sigma).hom := sorry

/-- The identity morphism of an equivariant system. -/
def id (D : System p rho) : Hom p rho D D where
  hom := 𝟙 D.obj
  compatibility := id_compatibility p rho D

/-- Compatibility with equivariance is preserved by composition. -/
theorem comp_compatibility (f : Hom p rho D E) (g : Hom p rho E K) (sigma : G) :
    (D.iso sigma).hom ≫
        (QCoh.pullback (actionHom p rho sigma)).map (f.hom ≫ g.hom) =
      (f.hom ≫ g.hom) ≫ (K.iso sigma).hom := sorry

/-- Composition of equivariant morphisms. -/
def comp (f : Hom p rho D E) (g : Hom p rho E K) : Hom p rho D K where
  hom := f.hom ≫ g.hom
  compatibility := comp_compatibility p rho f g

/-- Left identity for equivariant morphisms. -/
theorem id_comp (f : Hom p rho D E) : comp p rho (id p rho D) f = f := sorry

/-- Right identity for equivariant morphisms. -/
theorem comp_id (f : Hom p rho D E) : comp p rho f (id p rho E) = f := sorry

/-- Associativity for equivariant morphisms. -/
theorem assoc (f : Hom p rho D E) (g : Hom p rho E K) (h : Hom p rho K L) :
    comp p rho (comp p rho f g) h = comp p rho f (comp p rho g h) := sorry

end Hom

end System

/-- The explicit category structure on pullback-twisted equivariant systems. -/
@[reducible] def systemCategory : Category (System p rho) where
  Hom := System.Hom p rho
  id := System.Hom.id p rho
  comp := System.Hom.comp p rho
  id_comp := System.Hom.id_comp p rho
  comp_id := System.Hom.comp_id p rho
  assoc := System.Hom.assoc p rho

/-- The category of pullback-twisted `G`-equivariant quasi-coherent modules on `X`. -/
def Equivariant : Cat :=
  @Cat.of (System p rho) (systemCategory p rho)

namespace Equivariant

/-- Construct an object of `Equivariant p rho` from an explicit module, isomorphism family,
and cocycle. -/
def of (F : QCoh X)
    (phi : ∀ sigma : G, F ≅ (QCoh.pullback (actionHom p rho sigma)).obj F)
    (hphi : ∀ sigma tau : G,
      (phi (sigma * tau)).hom =
        (phi sigma).hom ≫
          (QCoh.pullback (actionHom p rho sigma)).map (phi tau).hom ≫
            (pullbackMulIso p rho sigma tau).hom.app F) : Equivariant p rho :=
  System.of p rho F phi hphi

/-- The underlying quasi-coherent module of an equivariant object. -/
def obj (D : Equivariant p rho) : QCoh X :=
  System.obj D

/-- The pullback-twisted isomorphism indexed by `sigma`. -/
def iso (D : Equivariant p rho) (sigma : G) :
    obj p rho D ≅ (QCoh.pullback (actionHom p rho sigma)).obj (obj p rho D) :=
  System.iso D sigma

/-- The underlying quasi-coherent-module map of an equivariant morphism. -/
def hom {D E : Equivariant p rho} (f : D ⟶ E) : obj p rho D ⟶ obj p rho E :=
  (f : System.Hom p rho D E).hom

/-- The isomorphisms of an equivariant object satisfy the transported cocycle equation. -/
theorem cocycle (D : Equivariant p rho) (sigma tau : G) :
    (iso p rho D (sigma * tau)).hom =
      (iso p rho D sigma).hom ≫
        (QCoh.pullback (actionHom p rho sigma)).map (iso p rho D tau).hom ≫
          (pullbackMulIso p rho sigma tau).hom.app (obj p rho D) := sorry

/-- An equivariant morphism commutes with every pullback-twisted isomorphism. -/
theorem hom_compatibility {D E : Equivariant p rho} (f : D ⟶ E) (sigma : G) :
    (iso p rho D sigma).hom ≫
        (QCoh.pullback (actionHom p rho sigma)).map (hom p rho f) =
      hom p rho f ≫ (iso p rho E sigma).hom := sorry

/-- Equivariant morphisms are determined by their underlying quasi-coherent-module maps. -/
theorem homExt {D E : Equivariant p rho} {f g : D ⟶ E}
    (h : hom p rho f = hom p rho g) : f = g := sorry

end Equivariant

/-- The quasi-coherent pullback of `F` along `p`. -/
noncomputable def descentObj (F : QCoh Y) : QCoh X :=
  (QCoh.pullback p).obj F

/-- The canonical equivariance isomorphism on the pullback of a module from `Y`. -/
noncomputable def descentIso (F : QCoh Y) (sigma : G) :
    descentObj p F ≅
      (QCoh.pullback (actionHom p rho sigma)).obj (descentObj p F) :=
  (Cat.Hom.toNatIso
    ((QCoh.pseudofunctor.map₂Iso
      (eqToIso
        (congrArg (fun f : X ⟶ Y ↦ f.op.toLoc)
          (actionHom_over p rho sigma)).symm)).trans
      (QCoh.pseudofunctor.mapComp p.op.toLoc
        (actionHom p rho sigma).op.toLoc))).app F

/-- The canonical pullback isomorphisms satisfy the equivariant cocycle equation. -/
theorem descentIso_cocycle (F : QCoh Y) (sigma tau : G) :
    (descentIso p rho F (sigma * tau)).hom =
      (descentIso p rho F sigma).hom ≫
        (QCoh.pullback (actionHom p rho sigma)).map
          (descentIso p rho F tau).hom ≫
            (pullbackMulIso p rho sigma tau).hom.app (descentObj p F) := sorry

/-- Pullback of a quasi-coherent module from `Y` as an equivariant system on `X`. -/
noncomputable def descentSystem (F : QCoh Y) : System p rho :=
  System.of p rho (descentObj p F) (descentIso p rho F) (descentIso_cocycle p rho F)

/-- Pullback of a morphism from `Y` commutes with the canonical equivariance isomorphisms. -/
theorem descentHom_compatibility {F H : QCoh Y} (f : F ⟶ H) (sigma : G) :
    ((descentSystem p rho F).iso sigma).hom ≫
        (QCoh.pullback (actionHom p rho sigma)).map ((QCoh.pullback p).map f) =
      (QCoh.pullback p).map f ≫ ((descentSystem p rho H).iso sigma).hom := sorry

/-- Pullback of a morphism from `Y` as a morphism of equivariant systems. -/
noncomputable def descentHom {F H : QCoh Y} (f : F ⟶ H) :
    System.Hom p rho (descentSystem p rho F) (descentSystem p rho H) where
  hom := (QCoh.pullback p).map f
  compatibility := descentHom_compatibility p rho f

/-- The pullback construction preserves identity morphisms. -/
theorem descentHom_id (F : QCoh Y) :
    descentHom p rho (𝟙 F) = System.Hom.id p rho (descentSystem p rho F) := sorry

/-- The pullback construction preserves composition. -/
theorem descentHom_comp {F H K : QCoh Y} (f : F ⟶ H) (g : H ⟶ K) :
    descentHom p rho (f ≫ g) =
      System.Hom.comp p rho (descentHom p rho f) (descentHom p rho g) := sorry

/-- The canonical descent functor from quasi-coherent modules on `Y` to equivariant
quasi-coherent modules on `X`. -/
noncomputable def descent : QCoh Y ⥤ Equivariant p rho where
  obj := descentSystem p rho
  map := descentHom p rho
  map_id := descentHom_id p rho
  map_comp := descentHom_comp p rho

/-- On objects, `descent` is the explicitly constructed pullback system. -/
theorem descent_obj (F : QCoh Y) :
    (descent p rho).obj F = descentSystem p rho F := sorry

/-- On morphisms, `descent` is pullback of the quasi-coherent-module morphism. -/
theorem descent_map {F H : QCoh Y} (f : F ⟶ H) :
    Equivariant.hom p rho ((descent p rho).map f) = (QCoh.pullback p).map f := sorry

/-- The equivariance isomorphism on `descent.obj F` is the canonical pullback comparison. -/
theorem descent_iso (F : QCoh Y) (sigma : G) :
    Equivariant.iso p rho ((descent p rho).obj F) sigma = descentIso p rho F sigma := sorry

end AlgebraicGeometry.Scheme.QCoh.GaloisDescent

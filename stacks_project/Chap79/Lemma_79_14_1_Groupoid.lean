/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap78.Definition_78_11_1_Groupoid
public import stacks_project.Chap79.Lemma_79_14_1_Section

/-!
# Finite-part groupoid in algebraic spaces

A groupoid in algebraic spaces over `B` whose source and target are separated and
locally of finite type has a finite-part groupoid `(U', Z_univ, s', t', c', e', i')`
and a canonical morphism to the original groupoid.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Limits Opposite
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

variable {S : Scheme.{u}} {B : AlgebraicSpace S}

/-- The identity-arrow map of `G` is a section of the source map on underlying
algebraic spaces. -/
theorem unit_source_left (G : GroupoidAlgebraicSpace B) :
    G.e.left ≫ G.s.left = 𝟙 G.U.left := sorry

/-- A `T`-point of the universal finite subspace: a with-section pair for `G.s`
together with an arrow `z` through that open. -/
structure ArrowPoint (G : GroupoidAlgebraicSpace B) (T : Over S)
    extends
      toWithSection :
        FinitePart.WithSection.Point G.s.left G.e.left (unit_source_left G) T where
  /-- The chosen arrow `z : T ⟶ R`. -/
  z : ofOver T ⟶ G.R.left
  /-- The source of `z` is the object map `a`. -/
  z_source : z ≫ G.s.left = a
  /-- The section `(1_T, z)` factors through `Z`. -/
  factors_z :
    ∃ ℓ : ofOver T ⟶ (OpenSubspace.ofOpens Z).X,
      ℓ ≫ (OpenSubspace.ofOpens Z).ι ≫ pullback.fst a G.s.left = 𝟙 (ofOver T) ∧
        ℓ ≫ (OpenSubspace.ofOpens Z).ι ≫ pullback.snd a G.s.left = z

/-- The pullback condition for the graph of an arrow point. -/
theorem arrowSection_condition (G : GroupoidAlgebraicSpace B) {T : Over S}
    (p : ArrowPoint G T) :
    𝟙 (ofOver T) ≫ p.a = p.z ≫ G.s.left := sorry

/-- The graph morphism `(1_T, z) : T ⟶ T ×_U R`. -/
def arrowSection (G : GroupoidAlgebraicSpace B) {T : Over S} (p : ArrowPoint G T) :
    ofOver T ⟶ pullback p.a G.s.left :=
  pullback.lift (𝟙 (ofOver T)) p.z (arrowSection_condition G p)

/-- Build an arrow point from a with-section pair and an arrow through its open. -/
def ArrowPoint.of (G : GroupoidAlgebraicSpace B) {T : Over S}
    (p : FinitePart.WithSection.Point G.s.left G.e.left (unit_source_left G) T)
    (z : ofOver T ⟶ G.R.left) (z_source : z ≫ G.s.left = p.a)
    (factors_z :
      ∃ ℓ : ofOver T ⟶ (OpenSubspace.ofOpens p.Z).X,
        ℓ ≫ (OpenSubspace.ofOpens p.Z).ι ≫ pullback.fst p.a G.s.left =
            𝟙 (ofOver T) ∧
          ℓ ≫ (OpenSubspace.ofOpens p.Z).ι ≫ pullback.snd p.a G.s.left = z) :
    ArrowPoint G T where
  toWithSection := p
  z := z
  z_source := z_source
  factors_z := factors_z

/-- An arrow point consists of a with-section pair and an arrow through its open. -/
theorem ArrowPoint.spec (G : GroupoidAlgebraicSpace B) {T : Over S}
    (p : ArrowPoint G T) :
    p.z ≫ G.s.left = p.a ∧
      Set.range (Points.map (arrowSection G p)) ⊆ p.Z := sorry

/-- The structure morphism `T ⟶ B` associated to an arrow point. -/
def pointToB (G : GroupoidAlgebraicSpace B) {T : Over S} (p : ArrowPoint G T) :
    ofOver T ⟶ B :=
  p.a ≫ G.U.hom

/-- The object of `Over B` associated to an arrow point. -/
def pointOver (G : GroupoidAlgebraicSpace B) {T : Over S} (p : ArrowPoint G T) :
    Over B :=
  Over.mk (pointToB G p)

/-- The arrow `z` is a morphism over `B`. -/
theorem zOver_w (G : GroupoidAlgebraicSpace B) {T : Over S} (p : ArrowPoint G T) :
    p.z ≫ G.R.hom = (pointOver G p).hom := sorry

/-- The arrow of an arrow point as a morphism in `Over B`. -/
def zOver (G : GroupoidAlgebraicSpace B) {T : Over S} (p : ArrowPoint G T) :
    pointOver G p ⟶ G.R :=
  Over.homMk p.z (zOver_w G p)

/-- The arrow of an arrow point as a morphism from `Over.mk σ`. -/
def zOverAs (G : GroupoidAlgebraicSpace B) {T : Over S} (p : ArrowPoint G T)
    (σ : ofOver T ⟶ B) (hσ : p.z ≫ G.R.hom = σ) : Over.mk σ ⟶ G.R :=
  Over.homMk p.z hσ

/-- The fibre product `T ×_U R` as an object over `B`. -/
def fiberOver (G : GroupoidAlgebraicSpace B) {T : Over S} (p : ArrowPoint G T) :
    Over B :=
  Over.mk (pullback.fst p.a G.s.left ≫ p.a ≫ G.U.hom)

/-- The later-arrow projection from the fibre is a morphism over `B`. -/
theorem laterOver_w (G : GroupoidAlgebraicSpace B) {T : Over S} (p : ArrowPoint G T) :
    pullback.snd p.a G.s.left ≫ G.R.hom = (fiberOver G p).hom := sorry

/-- The later arrow of a fibre point, as a morphism in `Over B`. -/
def laterOver (G : GroupoidAlgebraicSpace B) {T : Over S} (p : ArrowPoint G T) :
    fiberOver G p ⟶ G.R :=
  Over.homMk (pullback.snd p.a G.s.left) (laterOver_w G p)

/-- The earlier arrow `i ∘ z` from the fibre is a morphism over `B`. -/
theorem earlierOver_w (G : GroupoidAlgebraicSpace B) {T : Over S} (p : ArrowPoint G T) :
    (pullback.fst p.a G.s.left ≫ p.z ≫ G.i.left) ≫ G.R.hom =
      (fiberOver G p).hom := sorry

/-- The earlier arrow `i ∘ z` of a fibre point, as a morphism in `Over B`. -/
def earlierOver (G : GroupoidAlgebraicSpace B) {T : Over S} (p : ArrowPoint G T) :
    fiberOver G p ⟶ G.R :=
  Over.homMk (pullback.fst p.a G.s.left ≫ p.z ≫ G.i.left) (earlierOver_w G p)

/-- The later and earlier fibre arrows are composable. -/
theorem conjugate_compose_w (G : GroupoidAlgebraicSpace B) {T : Over S}
    (p : ArrowPoint G T) :
    laterOver G p ≫ G.s = earlierOver G p ≫ G.t := sorry

/-- Right multiplication by `i ∘ z` on the fibre of `s` over `a`. -/
def conjugateArrow (G : GroupoidAlgebraicSpace B) {T : Over S} (p : ArrowPoint G T) :
    fiberOver G p ⟶ G.R :=
  G.compose (laterOver G p) (earlierOver G p) (conjugate_compose_w G p)

/-- The conjugated arrow has source `t ∘ z`. -/
theorem conjugateMap_condition (G : GroupoidAlgebraicSpace B) {T : Over S}
    (p : ArrowPoint G T) :
    pullback.fst p.a G.s.left ≫ p.z ≫ G.t.left =
      (conjugateArrow G p).left ≫ G.s.left := sorry

/-- The conjugation isomorphism on fibres `c(-, i ∘ z)`. -/
def conjugateMap (G : GroupoidAlgebraicSpace B) {T : Over S} (p : ArrowPoint G T) :
    pullback p.a G.s.left ⟶ pullback (p.z ≫ G.t.left) G.s.left :=
  pullback.lift (pullback.fst p.a G.s.left) (conjugateArrow G p).left
    (conjugateMap_condition G p)

/-- The open obtained by conjugating `Z` along `c(-, i ∘ z)`. -/
def conjugateOpen (G : GroupoidAlgebraicSpace B) {T : Over S} (p : ArrowPoint G T) :
    Opens (Points (pullback (p.z ≫ G.t.left) G.s.left)) where
  carrier := Set.image (Points.map (conjugateMap G p)) p.Z
  is_open' := sorry

/-- The target with-section pair `(t ∘ z, c(Z, i ∘ z))`. -/
def targetPoint (G : GroupoidAlgebraicSpace B) {T : Over S} (p : ArrowPoint G T) :
    FinitePart.WithSection.Point G.s.left G.e.left (unit_source_left G) T where
  a := p.z ≫ G.t.left
  Z := conjugateOpen G p
  isFinite := sorry
  contains_unit := sorry

/-- The inverse arrow point `(t ∘ z, c(Z, i ∘ z), i ∘ z)`. -/
def inversePoint (G : GroupoidAlgebraicSpace B) {T : Over S} (p : ArrowPoint G T) :
    ArrowPoint G T where
  toWithSection := targetPoint G p
  z := p.z ≫ G.i.left
  z_source := sorry
  factors_z := sorry

/-- The identity arrow point `(a, Z, e ∘ a)`. -/
def unitPoint (G : GroupoidAlgebraicSpace B) {T : Over S}
    (p : FinitePart.WithSection.Point G.s.left G.e.left (unit_source_left G) T) :
    ArrowPoint G T where
  toWithSection := p
  z := p.a ≫ G.e.left
  z_source := sorry
  factors_z := sorry

/-- Compatible arrow points determine the same structure morphism to `B`. -/
theorem composePoint_over (G : GroupoidAlgebraicSpace B) {T : Over S}
    (later earlier : ArrowPoint G T)
    (h_over : later.a ≫ G.U.hom = earlier.a ≫ G.U.hom) :
    later.z ≫ G.R.hom = pointToB G earlier := sorry

/-- The later and earlier arrows of a composable pair of arrow points are composable. -/
theorem composePoint_w (G : GroupoidAlgebraicSpace B) {T : Over S}
    (later earlier : ArrowPoint G T)
    (h_over : later.a ≫ G.U.hom = earlier.a ≫ G.U.hom)
    (h_comp : later.z ≫ G.s.left = earlier.z ≫ G.t.left) :
    zOverAs G later (pointToB G earlier) (composePoint_over G later earlier h_over) ≫
        G.s =
      zOver G earlier ≫ G.t := sorry

/-- The composite arrow point `(u₂, Z₂, z₁ ∘ z₂)` of a composable pair. -/
def composePoint (G : GroupoidAlgebraicSpace B) {T : Over S}
    (later earlier : ArrowPoint G T)
    (h_over : later.a ≫ G.U.hom = earlier.a ≫ G.U.hom)
    (h_comp : later.z ≫ G.s.left = earlier.z ≫ G.t.left) : ArrowPoint G T where
  toWithSection := earlier.toWithSection
  z :=
    (G.compose
        (zOverAs G later (pointToB G earlier)
          (composePoint_over G later earlier h_over))
        (zOver G earlier) (composePoint_w G later earlier h_over h_comp)).left
  z_source := sorry
  factors_z := sorry

/-- Base change of an arrow point along `h : T' ⟶ T`. -/
def ArrowPoint.restrict (G : GroupoidAlgebraicSpace B) {T T' : Over S}
    (p : ArrowPoint G T) (h : T' ⟶ T) : ArrowPoint G T' where
  toWithSection := p.toWithSection.restrict h
  z := ofOverMap h ≫ p.z
  z_source := sorry
  factors_z := sorry

/-- The type of arrow points over a scheme `T` is `u`-small. -/
instance instSmall_arrowPoint (G : GroupoidAlgebraicSpace B) (T : Over S) :
    Small.{u} (ArrowPoint G T) := sorry

variable (G : GroupoidAlgebraicSpace B)

/-- The functor of `T`-points of the universal finite subspace `Z_univ`. -/
def arrowFunctor : (Over S)ᵒᵖ ⥤ Type u where
  obj T := Shrink (ArrowPoint G T.unop)
  map {T T'} h :=
    TypeCat.ofHom fun p ↦
      equivShrink (ArrowPoint G T'.unop)
        (ArrowPoint.restrict G ((equivShrink (ArrowPoint G T.unop)).symm p) h.unop)
  map_id := sorry
  map_comp := sorry

/-- Values of the arrow functor are equivalent to arrow points. -/
def arrowFunctor_obj_equiv (T : Over S) :
    (arrowFunctor G).obj (op T) ≃ ArrowPoint G T :=
  (equivShrink (ArrowPoint G T)).symm

variable [AlgebraicSpace.Separated G.s.left] [AlgebraicSpace.LocallyOfFiniteType G.s.left]
variable [AlgebraicSpace.Separated G.t.left] [AlgebraicSpace.LocallyOfFiniteType G.t.left]

/-- The algebraic space underlying `Z_univ`. -/
def univSpace : AlgebraicSpace S :=
  ofFunctor (arrowFunctor G) sorry sorry sorry

/-- The functor of points of `univSpace G` is the arrow functor. -/
theorem univSpace_functorOfPoints : (univSpace G).functorOfPoints = arrowFunctor G := sorry

/-- The morphism `g : U' ⟶ U` from the finite-part-with-section space of `G.s`. -/
def finitePartToU :
    FinitePart.withSectionSpace G.s.left G.e.left (unit_source_left G) ⟶ G.U.left :=
  FinitePart.withSectionToY G.s.left G.e.left (unit_source_left G)

/-- Recover a with-section pair from a morphism into the with-section space. -/
def withSectionOfHom {T : Over S}
    (f : ofOver T ⟶
      FinitePart.withSectionSpace G.s.left G.e.left (unit_source_left G)) :
    FinitePart.WithSection.Point G.s.left G.e.left (unit_source_left G) T :=
  (equivShrink
      (FinitePart.WithSection.Point G.s.left G.e.left (unit_source_left G) T)).symm
    (yonedaEquiv
      (f :
        yoneda.obj T ⟶
          (FinitePart.withSectionSpace G.s.left G.e.left
              (unit_source_left G)).functorOfPoints))

/-- The classifying morphism of a with-section pair. -/
def withSectionHom {T : Over S}
    (p : FinitePart.WithSection.Point G.s.left G.e.left (unit_source_left G) T) :
    ofOver T ⟶ FinitePart.withSectionSpace G.s.left G.e.left (unit_source_left G) :=
  (yonedaEquiv.symm
      (equivShrink
          (FinitePart.WithSection.Point G.s.left G.e.left (unit_source_left G) T)
          p) :
    ofOver T ⟶
      FinitePart.withSectionSpace G.s.left G.e.left (unit_source_left G))

/-- The classifying morphism of a with-section pair recovers the object map `a`. -/
theorem withSectionHom_toU {T : Over S}
    (p : FinitePart.WithSection.Point G.s.left G.e.left (unit_source_left G) T) :
    withSectionHom G p ≫ finitePartToU G = p.a := sorry

/-- Recover an arrow point from a morphism into `univSpace G`. -/
def arrowPointOfHom {T : Over S} (f : ofOver T ⟶ univSpace G) : ArrowPoint G T :=
  (equivShrink (ArrowPoint G T)).symm
    (yonedaEquiv (f : yoneda.obj T ⟶ (univSpace G).functorOfPoints))

/-- The two legs of an arrow point agree over `U`, inducing a map to the fibre product. -/
theorem univιPoint_condition {T : Over S} (p : ArrowPoint G T) :
    withSectionHom G p.toWithSection ≫ finitePartToU G = p.z ≫ G.s.left := sorry

/-- The map `T ⟶ U' ×_U R` associated to an arrow point. -/
def univιPoint {T : Over S} (p : ArrowPoint G T) :
    ofOver T ⟶ pullback (finitePartToU G) G.s.left :=
  pullback.lift (withSectionHom G p.toWithSection) p.z (univιPoint_condition G p)

/-- A with-section pair and an arrow over `a` induce a map to `U' ×_U R`. -/
theorem univPoint_condition {T : Over S}
    (p : FinitePart.WithSection.Point G.s.left G.e.left (unit_source_left G) T)
    (z : ofOver T ⟶ G.R.left) (hz : z ≫ G.s.left = p.a) :
    withSectionHom G p ≫ finitePartToU G = z ≫ G.s.left := sorry

/-- The `T`-point of `U' ×_U R` associated to a with-section pair and an arrow. -/
def univPoint {T : Over S}
    (p : FinitePart.WithSection.Point G.s.left G.e.left (unit_source_left G) T)
    (z : ofOver T ⟶ G.R.left) (hz : z ≫ G.s.left = p.a) :
    ofOver T ⟶ pullback (finitePartToU G) G.s.left :=
  pullback.lift (withSectionHom G p) z (univPoint_condition G p z hz)

/-- The first projection of `univPoint G p z hz` is the classifying map of `p`. -/
theorem univPoint_fst {T : Over S}
    (p : FinitePart.WithSection.Point G.s.left G.e.left (unit_source_left G) T)
    (z : ofOver T ⟶ G.R.left) (hz : z ≫ G.s.left = p.a) :
    univPoint G p z hz ≫ pullback.fst (finitePartToU G) G.s.left =
      withSectionHom G p := sorry

/-- The second projection of `univPoint G p z hz` is the arrow `z`. -/
theorem univPoint_snd {T : Over S}
    (p : FinitePart.WithSection.Point G.s.left G.e.left (unit_source_left G) T)
    (z : ofOver T ⟶ G.R.left) (hz : z ≫ G.s.left = p.a) :
    univPoint G p z hz ≫ pullback.snd (finitePartToU G) G.s.left = z := sorry

/-- The inclusion `Z_univ ⊂ U' ×_{g, U, s} R`. -/
def univι : univSpace G ⟶ pullback (finitePartToU G) G.s.left where
  app T :=
    TypeCat.ofHom fun p ↦
      yonedaEquiv
        (univιPoint G ((equivShrink (ArrowPoint G T.unop)).symm p) :
          yoneda.obj T.unop ⟶ (pullback (finitePartToU G) G.s.left).functorOfPoints)
  naturality := sorry

/-- The graph of `z` factors through the open `p.Z ⊂ |T ×_U R|`. -/
def factorsThroughOpen {T : Over S}
    (p : FinitePart.WithSection.Point G.s.left G.e.left (unit_source_left G) T)
    (z : ofOver T ⟶ G.R.left) : Prop :=
  ∃ ℓ : ofOver T ⟶ (OpenSubspace.ofOpens p.Z).X,
    ℓ ≫ (OpenSubspace.ofOpens p.Z).ι ≫ pullback.fst p.a G.s.left = 𝟙 (ofOver T) ∧
      ℓ ≫ (OpenSubspace.ofOpens p.Z).ι ≫ pullback.snd p.a G.s.left = z

/-- A morphism into `U' ×_U R` factors through `Z_univ`. -/
def factorsThroughUnivι {T : Over S}
    (q : ofOver T ⟶ pullback (finitePartToU G) G.s.left) : Prop :=
  ∃ ℓ : ofOver T ⟶ univSpace G, ℓ ≫ univι G = q

/-- The forgetful map `Z_univ ⟶ U'` on underlying algebraic spaces. -/
def sourceLeft :
    univSpace G ⟶ FinitePart.withSectionSpace G.s.left G.e.left (unit_source_left G) where
  app T :=
    TypeCat.ofHom fun p ↦
      equivShrink
          (FinitePart.WithSection.Point G.s.left G.e.left (unit_source_left G) T.unop)
        ((equivShrink (ArrowPoint G T.unop)).symm p).toWithSection
  naturality := sorry

/-- The target map `Z_univ ⟶ U'` on underlying algebraic spaces. -/
def targetLeft :
    univSpace G ⟶ FinitePart.withSectionSpace G.s.left G.e.left (unit_source_left G) where
  app T :=
    TypeCat.ofHom fun p ↦
      equivShrink
          (FinitePart.WithSection.Point G.s.left G.e.left (unit_source_left G) T.unop)
        (targetPoint G ((equivShrink (ArrowPoint G T.unop)).symm p))
  naturality := sorry

/-- The identity-arrow map `U' ⟶ Z_univ` on underlying algebraic spaces. -/
def unitLeft :
    FinitePart.withSectionSpace G.s.left G.e.left (unit_source_left G) ⟶ univSpace G where
  app T :=
    TypeCat.ofHom fun p ↦
      equivShrink (ArrowPoint G T.unop)
        (unitPoint G
          ((equivShrink
                (FinitePart.WithSection.Point G.s.left G.e.left
                    (unit_source_left G) T.unop)).symm
            p))
  naturality := sorry

/-- The inverse-arrow map of `Z_univ` on underlying algebraic spaces. -/
def inverseLeft : univSpace G ⟶ univSpace G where
  app T :=
    TypeCat.ofHom fun p ↦
      equivShrink (ArrowPoint G T.unop)
        (inversePoint G ((equivShrink (ArrowPoint G T.unop)).symm p))
  naturality := sorry

/-- The arrow map `Z_univ ⟶ R` sending `(u, Z, z)` to `z`. -/
def univToR : univSpace G ⟶ G.R.left :=
  univι G ≫ pullback.snd (finitePartToU G) G.s.left

/-- The structure morphism of `Z_univ` over `B`. -/
def univToB : univSpace G ⟶ B :=
  univToR G ≫ G.R.hom

/-- The object space `U'` of the finite-part groupoid, as an object over `B`. -/
def finitePartObject : Over B :=
  Over.mk (finitePartToU G ≫ G.U.hom)

/-- The arrow space `Z_univ` of the finite-part groupoid, as an object over `B`. -/
def finitePartArrow : Over B :=
  Over.mk (univToB G)

/-- The source map of the finite-part groupoid lies over `B`. -/
theorem finitePart_s_w : sourceLeft G ≫ (finitePartObject G).hom = (finitePartArrow G).hom :=
  sorry

/-- The source map `s' : Z_univ ⟶ U'`. -/
def finitePart_s : finitePartArrow G ⟶ finitePartObject G :=
  Over.homMk (sourceLeft G) (finitePart_s_w G)

/-- The target map of the finite-part groupoid lies over `B`. -/
theorem finitePart_t_w : targetLeft G ≫ (finitePartObject G).hom = (finitePartArrow G).hom :=
  sorry

/-- The target map `t' : Z_univ ⟶ U'`. -/
def finitePart_t : finitePartArrow G ⟶ finitePartObject G :=
  Over.homMk (targetLeft G) (finitePart_t_w G)

/-- The identity map of the finite-part groupoid lies over `B`. -/
theorem finitePart_e_w : unitLeft G ≫ (finitePartArrow G).hom = (finitePartObject G).hom :=
  sorry

/-- The identity-arrow map `e' : U' ⟶ Z_univ`. -/
def finitePart_e : finitePartObject G ⟶ finitePartArrow G :=
  Over.homMk (unitLeft G) (finitePart_e_w G)

/-- The inverse map of the finite-part groupoid lies over `B`. -/
theorem finitePart_i_w : inverseLeft G ≫ (finitePartArrow G).hom = (finitePartArrow G).hom :=
  sorry

/-- The inverse-arrow map `i' : Z_univ ⟶ Z_univ`. -/
def finitePart_i : finitePartArrow G ⟶ finitePartArrow G :=
  Over.homMk (inverseLeft G) (finitePart_i_w G)

/-- The later arrow point of a morphism into the composable-arrow pullback. -/
def laterPointOfHom {T : Over S}
    (f : ofOver T ⟶ (pullback (finitePart_s G) (finitePart_t G)).left) :
    ArrowPoint G T :=
  arrowPointOfHom G (f ≫ (pullback.fst (finitePart_s G) (finitePart_t G)).left)

/-- The earlier arrow point of a morphism into the composable-arrow pullback. -/
def earlierPointOfHom {T : Over S}
    (f : ofOver T ⟶ (pullback (finitePart_s G) (finitePart_t G)).left) :
    ArrowPoint G T :=
  arrowPointOfHom G (f ≫ (pullback.snd (finitePart_s G) (finitePart_t G)).left)

/-- Composable finite-part arrows lie over the same object of `B`. -/
theorem laterPointOfHom_over {T : Over S}
    (f : ofOver T ⟶ (pullback (finitePart_s G) (finitePart_t G)).left) :
    (laterPointOfHom G f).a ≫ G.U.hom = (earlierPointOfHom G f).a ≫ G.U.hom :=
  sorry

/-- The later and earlier arrows of a composable pair of finite-part arrows
are composable. -/
theorem laterPointOfHom_comp {T : Over S}
    (f : ofOver T ⟶ (pullback (finitePart_s G) (finitePart_t G)).left) :
    (laterPointOfHom G f).z ≫ G.s.left = (earlierPointOfHom G f).z ≫ G.t.left :=
  sorry

/-- The composite arrow point of a morphism into the composable-arrow pullback. -/
def composePointOfHom {T : Over S}
    (f : ofOver T ⟶ (pullback (finitePart_s G) (finitePart_t G)).left) :
    ArrowPoint G T :=
  composePoint G (laterPointOfHom G f) (earlierPointOfHom G f)
    (laterPointOfHom_over G f) (laterPointOfHom_comp G f)

/-- The composition map of the finite-part groupoid on underlying algebraic spaces. -/
def compositionLeft :
    (pullback (finitePart_s G) (finitePart_t G)).left ⟶ univSpace G where
  app T :=
    TypeCat.ofHom fun φ ↦
      equivShrink (ArrowPoint G T.unop)
        (composePointOfHom G
          (yonedaEquiv.symm φ :
            ofOver T.unop ⟶ (pullback (finitePart_s G) (finitePart_t G)).left))
  naturality := sorry

/-- The composition map of the finite-part groupoid lies over `B`. -/
theorem finitePart_c_w :
    compositionLeft G ≫ (finitePartArrow G).hom =
      (pullback (finitePart_s G) (finitePart_t G)).hom := sorry

/-- The composition map `c'` of the finite-part groupoid. -/
def finitePart_c : pullback (finitePart_s G) (finitePart_t G) ⟶ finitePartArrow G :=
  Over.homMk (compositionLeft G) (finitePart_c_w G)

/-- The finite-part groupoid of a groupoid in algebraic spaces over `B`. -/
def finitePart : GroupoidAlgebraicSpace B where
  U := finitePartObject G
  R := finitePartArrow G
  s := finitePart_s G
  t := finitePart_t G
  c := finitePart_c G
  e := finitePart_e G
  i := finitePart_i G
  comp_source := sorry
  comp_target := sorry
  identity_source := sorry
  identity_target := sorry
  inverse_source := sorry
  inverse_target := sorry
  associativity := sorry
  right_identity := sorry
  left_identity := sorry
  inverse_comp := sorry
  comp_inverse := sorry

/-- The object space of the finite-part groupoid is the with-section finite-part space. -/
theorem finitePart_U :
    (finitePart G).U.left =
      FinitePart.withSectionSpace G.s.left G.e.left (unit_source_left G) := sorry

/-- The arrow space of the finite-part groupoid is `univSpace G`. -/
theorem finitePart_R : (finitePart G).R.left = univSpace G := sorry

/-- The object component of the canonical morphism lies over `B`. -/
theorem finitePartHom_obj_w :
    finitePartToU G ≫ G.U.hom = (finitePart G).U.hom := sorry

/-- The arrow component of the canonical morphism lies over `B`. -/
theorem finitePartHom_arrow_w : univToR G ≫ G.R.hom = (finitePart G).R.hom := sorry

/-- The canonical morphism from the finite-part groupoid to `G`. -/
def finitePartHom : Hom (finitePart G) G where
  obj := Over.homMk (finitePartToU G) (finitePartHom_obj_w G)
  arrow := Over.homMk (univToR G) (finitePartHom_arrow_w G)
  map_s := sorry
  map_t := sorry
  map_c := sorry

/-- The object map of `finitePartHom G` is `g : U' ⟶ U`. -/
theorem finitePartHom_obj_left :
    (finitePartHom G).obj.left = finitePartToU G := sorry

/-- The arrow map of `finitePartHom G` sends `(u, Z, z)` to `z`. -/
theorem finitePartHom_arrow_left : (finitePartHom G).arrow.left = univToR G := sorry

/-- The morphism `g : U' ⟶ U` is étale. -/
instance etale_finitePartHom_obj : AlgebraicSpace.Etale (finitePartHom G).obj.left := sorry

/-- The graph of the base change of `e` along `g`. -/
theorem unitBaseChange_condition :
    𝟙 (FinitePart.withSectionSpace G.s.left G.e.left (unit_source_left G)) ≫
        finitePartToU G =
      (finitePartToU G ≫ G.e.left) ≫ G.s.left := sorry

/-- The base change of the unit `e` along `g : U' ⟶ U`. -/
def unitBaseChange :
    FinitePart.withSectionSpace G.s.left G.e.left (unit_source_left G) ⟶
      pullback (finitePartToU G) G.s.left :=
  pullback.lift (𝟙 _) (finitePartToU G ≫ G.e.left) (unitBaseChange_condition G)

/-- The base change of `e` factors through `Z_univ`. -/
theorem unitBaseChange_factors : unitLeft G ≫ univι G = unitBaseChange G := sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace

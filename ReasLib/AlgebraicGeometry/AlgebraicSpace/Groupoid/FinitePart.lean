module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FinitePart.WithSection

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
    G.e.left ≫ G.s.left = 𝟙 G.U.left := by
  exact congrArg (fun f ↦ f.left) G.identity_source

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
    ∃ ℓ : ofOver T ⟶ (OpenSubspace.fromOpens Z).X,
      ℓ ≫ (OpenSubspace.fromOpens Z).ι ≫ pullback.fst a G.s.left = 𝟙 (ofOver T) ∧
        ℓ ≫ (OpenSubspace.fromOpens Z).ι ≫ pullback.snd a G.s.left = z

/-- The pullback condition for the graph of an arrow point. -/
private theorem arrowSection_condition (G : GroupoidAlgebraicSpace B) {T : Over S}
    (p : ArrowPoint G T) :
    𝟙 (ofOver T) ≫ p.a = p.z ≫ G.s.left := by
  simpa only [Category.id_comp] using p.z_source.symm

/-- The graph morphism `(1_T, z) : T ⟶ T ×_U R`. -/
@[no_expose]
def arrowSection (G : GroupoidAlgebraicSpace B) {T : Over S} (p : ArrowPoint G T) :
    ofOver T ⟶ pullback p.a G.s.left :=
  pullback.lift (𝟙 (ofOver T)) p.z (arrowSection_condition G p)

/-- Build an arrow point from a with-section pair and an arrow through its open. -/
@[no_expose]
def ArrowPoint.of (G : GroupoidAlgebraicSpace B) {T : Over S}
    (p : FinitePart.WithSection.Point G.s.left G.e.left (unit_source_left G) T)
    (z : ofOver T ⟶ G.R.left) (z_source : z ≫ G.s.left = p.a)
    (factors_z :
      ∃ ℓ : ofOver T ⟶ (OpenSubspace.fromOpens p.Z).X,
        ℓ ≫ (OpenSubspace.fromOpens p.Z).ι ≫ pullback.fst p.a G.s.left =
            𝟙 (ofOver T) ∧
          ℓ ≫ (OpenSubspace.fromOpens p.Z).ι ≫ pullback.snd p.a G.s.left = z) :
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
private def pointToB (G : GroupoidAlgebraicSpace B) {T : Over S} (p : ArrowPoint G T) :
    ofOver T ⟶ B :=
  p.a ≫ G.U.hom

/-- The object of `Over B` associated to an arrow point. -/
private def pointOver (G : GroupoidAlgebraicSpace B) {T : Over S} (p : ArrowPoint G T) :
    Over B :=
  Over.mk (pointToB G p)

/-- The arrow `z` is a morphism over `B`. -/
private theorem zOver_w (G : GroupoidAlgebraicSpace B) {T : Over S} (p : ArrowPoint G T) :
    p.z ≫ G.R.hom = (pointOver G p).hom := by
  change p.z ≫ G.R.hom = p.a ≫ G.U.hom
  rw [← Over.w G.s, ← Category.assoc, p.z_source]

/-- The arrow of an arrow point as a morphism in `Over B`. -/
private def zOver (G : GroupoidAlgebraicSpace B) {T : Over S} (p : ArrowPoint G T) :
    pointOver G p ⟶ G.R :=
  Over.homMk p.z (zOver_w G p)

/-- The arrow of an arrow point as a morphism from `Over.mk σ`. -/
private def zOverAs (G : GroupoidAlgebraicSpace B) {T : Over S} (p : ArrowPoint G T)
    (σ : ofOver T ⟶ B) (hσ : p.z ≫ G.R.hom = σ) : Over.mk σ ⟶ G.R :=
  Over.homMk p.z hσ

/-- The fibre product `T ×_U R` as an object over `B`. -/
private def fiberOver (G : GroupoidAlgebraicSpace B) {T : Over S} (p : ArrowPoint G T) :
    Over B :=
  Over.mk (pullback.fst p.a G.s.left ≫ p.a ≫ G.U.hom)

/-- The later-arrow projection from the fibre is a morphism over `B`. -/
private theorem laterOver_w (G : GroupoidAlgebraicSpace B) {T : Over S} (p : ArrowPoint G T) :
    pullback.snd p.a G.s.left ≫ G.R.hom = (fiberOver G p).hom := by
  change pullback.snd p.a G.s.left ≫ G.R.hom =
    pullback.fst p.a G.s.left ≫ p.a ≫ G.U.hom
  rw [← Over.w G.s, ← Category.assoc, ← pullback.condition, Category.assoc]

/-- The later arrow of a fibre point, as a morphism in `Over B`. -/
private def laterOver (G : GroupoidAlgebraicSpace B) {T : Over S} (p : ArrowPoint G T) :
    fiberOver G p ⟶ G.R :=
  Over.homMk (pullback.snd p.a G.s.left) (laterOver_w G p)

/-- The earlier arrow `i ∘ z` from the fibre is a morphism over `B`. -/
private theorem earlierOver_w (G : GroupoidAlgebraicSpace B) {T : Over S} (p : ArrowPoint G T) :
    (pullback.fst p.a G.s.left ≫ p.z ≫ G.i.left) ≫ G.R.hom =
      (fiberOver G p).hom := by
  change (pullback.fst p.a G.s.left ≫ p.z ≫ G.i.left) ≫ G.R.hom =
    pullback.fst p.a G.s.left ≫ p.a ≫ G.U.hom
  simp only [Category.assoc, Over.w G.i]
  rw [show p.z ≫ G.R.hom = p.a ≫ G.U.hom from zOver_w G p]

/-- The earlier arrow `i ∘ z` of a fibre point, as a morphism in `Over B`. -/
private def earlierOver (G : GroupoidAlgebraicSpace B) {T : Over S} (p : ArrowPoint G T) :
    fiberOver G p ⟶ G.R :=
  Over.homMk (pullback.fst p.a G.s.left ≫ p.z ≫ G.i.left) (earlierOver_w G p)

/-- The later and earlier fibre arrows are composable. -/
private theorem conjugate_compose_w (G : GroupoidAlgebraicSpace B) {T : Over S}
    (p : ArrowPoint G T) :
    laterOver G p ≫ G.s = earlierOver G p ≫ G.t := by
  apply Over.OverMorphism.ext
  change pullback.snd p.a G.s.left ≫ G.s.left =
    (pullback.fst p.a G.s.left ≫ p.z ≫ G.i.left) ≫ G.t.left
  have hi : G.i.left ≫ G.t.left = G.s.left :=
    congrArg (fun f ↦ f.left) G.inverse_target
  rw [Category.assoc, Category.assoc, hi, p.z_source, pullback.condition]

/-- Right multiplication by `i ∘ z` on the fibre of `s` over `a`. -/
private def conjugateArrow (G : GroupoidAlgebraicSpace B) {T : Over S} (p : ArrowPoint G T) :
    fiberOver G p ⟶ G.R :=
  G.compose (laterOver G p) (earlierOver G p) (conjugate_compose_w G p)

/-- The conjugated arrow has source `t ∘ z`. -/
private theorem conjugateMap_condition (G : GroupoidAlgebraicSpace B) {T : Over S}
    (p : ArrowPoint G T) :
    pullback.fst p.a G.s.left ≫ p.z ≫ G.t.left =
      (conjugateArrow G p).left ≫ G.s.left := by
  change _ = (conjugateArrow G p ≫ G.s).left
  rw [show conjugateArrow G p ≫ G.s = earlierOver G p ≫ G.s from
    G.compose_source _ _ _]
  change _ = (pullback.fst p.a G.s.left ≫ p.z ≫ G.i.left) ≫ G.s.left
  have hi : G.i.left ≫ G.s.left = G.t.left :=
    congrArg (fun f ↦ f.left) G.inverse_source
  simp only [Category.assoc, hi]

/-- The conjugation isomorphism on fibres `c(-, i ∘ z)`. -/
private def conjugateMap (G : GroupoidAlgebraicSpace B) {T : Over S} (p : ArrowPoint G T) :
    pullback p.a G.s.left ⟶ pullback (p.z ≫ G.t.left) G.s.left :=
  pullback.lift (pullback.fst p.a G.s.left) (conjugateArrow G p).left
    (conjugateMap_condition G p)

private theorem conjugateOpen_isOpen (G : GroupoidAlgebraicSpace B) {T : Over S}
    (p : ArrowPoint G T) : IsOpen (Set.image (Points.map (conjugateMap G p)) p.Z) := sorry

/-- The open obtained by conjugating `Z` along `c(-, i ∘ z)`. -/
@[no_expose]
def conjugateOpen (G : GroupoidAlgebraicSpace B) {T : Over S} (p : ArrowPoint G T) :
    Opens (Points (pullback (p.z ≫ G.t.left) G.s.left)) where
  carrier := Set.image (Points.map (conjugateMap G p)) p.Z
  is_open' := conjugateOpen_isOpen G p

private theorem targetPoint_isFinite (G : GroupoidAlgebraicSpace B) {T : Over S}
    (p : ArrowPoint G T) :
    AlgebraicSpace.IsFinite ((OpenSubspace.fromOpens (conjugateOpen G p)).ι ≫
      pullback.fst (p.z ≫ G.t.left) G.s.left) := sorry

private theorem targetPoint_contains_unit (G : GroupoidAlgebraicSpace B) {T : Over S}
    (p : ArrowPoint G T) :
    Set.range (Points.map (FinitePart.unitSection (p.z ≫ G.t.left)
      G.s.left G.e.left (unit_source_left G))) ⊆ conjugateOpen G p := sorry

/-- The target with-section pair `(t ∘ z, c(Z, i ∘ z))`. -/
@[no_expose]
def targetPoint (G : GroupoidAlgebraicSpace B) {T : Over S} (p : ArrowPoint G T) :
    FinitePart.WithSection.Point G.s.left G.e.left (unit_source_left G) T where
  a := p.z ≫ G.t.left
  Z := conjugateOpen G p
  isFinite := targetPoint_isFinite G p
  contains_unit := targetPoint_contains_unit G p

private theorem inversePoint_factors_z (G : GroupoidAlgebraicSpace B) {T : Over S}
    (p : ArrowPoint G T) :
    ∃ ℓ : ofOver T ⟶ (OpenSubspace.fromOpens (targetPoint G p).Z).X,
      ℓ ≫ (OpenSubspace.fromOpens (targetPoint G p).Z).ι ≫ pullback.fst (targetPoint G p).a G.s.left = 𝟙 (ofOver T) ∧
        ℓ ≫ (OpenSubspace.fromOpens (targetPoint G p).Z).ι ≫ pullback.snd (targetPoint G p).a G.s.left = p.z ≫ G.i.left := sorry

/-- The inverse arrow point `(t ∘ z, c(Z, i ∘ z), i ∘ z)`. -/
@[no_expose]
def inversePoint (G : GroupoidAlgebraicSpace B) {T : Over S} (p : ArrowPoint G T) :
    ArrowPoint G T where
  toWithSection := targetPoint G p
  z := p.z ≫ G.i.left
  z_source := by
    change (p.z ≫ G.i.left) ≫ G.s.left = p.z ≫ G.t.left
    rw [Category.assoc, show G.i.left ≫ G.s.left = G.t.left from
      congrArg (fun f ↦ f.left) G.inverse_source]
  factors_z := inversePoint_factors_z G p

private theorem unitPoint_factors_z (G : GroupoidAlgebraicSpace B) {T : Over S}
    (p : FinitePart.WithSection.Point G.s.left G.e.left (unit_source_left G) T) :
    ∃ ℓ : ofOver T ⟶ (OpenSubspace.fromOpens p.Z).X,
      ℓ ≫ (OpenSubspace.fromOpens p.Z).ι ≫ pullback.fst p.a G.s.left = 𝟙 (ofOver T) ∧
        ℓ ≫ (OpenSubspace.fromOpens p.Z).ι ≫ pullback.snd p.a G.s.left = p.a ≫ G.e.left := sorry

/-- The identity arrow point `(a, Z, e ∘ a)`. -/
@[no_expose]
def unitPoint (G : GroupoidAlgebraicSpace B) {T : Over S}
    (p : FinitePart.WithSection.Point G.s.left G.e.left (unit_source_left G) T) :
    ArrowPoint G T where
  toWithSection := p
  z := p.a ≫ G.e.left
  z_source := by rw [Category.assoc, unit_source_left, Category.comp_id]
  factors_z := unitPoint_factors_z G p

/-- Compatible arrow points determine the same structure morphism to `B`. -/
private theorem composePoint_over (G : GroupoidAlgebraicSpace B) {T : Over S}
    (later earlier : ArrowPoint G T)
    (h_over : later.a ≫ G.U.hom = earlier.a ≫ G.U.hom) :
    later.z ≫ G.R.hom = pointToB G earlier := by
  exact (zOver_w G later).trans h_over

/-- The later and earlier arrows of a composable pair of arrow points are composable. -/
private theorem composePoint_w (G : GroupoidAlgebraicSpace B) {T : Over S}
    (later earlier : ArrowPoint G T)
    (h_over : later.a ≫ G.U.hom = earlier.a ≫ G.U.hom)
    (h_comp : later.z ≫ G.s.left = earlier.z ≫ G.t.left) :
    zOverAs G later (pointToB G earlier) (composePoint_over G later earlier h_over) ≫
        G.s =
      zOver G earlier ≫ G.t := by
  apply Over.OverMorphism.ext
  exact h_comp

private theorem composePoint_factors_z (G : GroupoidAlgebraicSpace B) {T : Over S}
    (later earlier : ArrowPoint G T)
    (h_over : later.a ≫ G.U.hom = earlier.a ≫ G.U.hom)
    (h_comp : later.z ≫ G.s.left = earlier.z ≫ G.t.left)
    (h_family : later.toWithSection = targetPoint G earlier) :
    ∃ ℓ : ofOver T ⟶ (OpenSubspace.fromOpens earlier.Z).X,
      ℓ ≫ (OpenSubspace.fromOpens earlier.Z).ι ≫ pullback.fst earlier.a G.s.left = 𝟙 (ofOver T) ∧
        ℓ ≫ (OpenSubspace.fromOpens earlier.Z).ι ≫ pullback.snd earlier.a G.s.left = (G.compose
        (zOverAs G later (pointToB G earlier)
          (composePoint_over G later earlier h_over))
        (zOver G earlier) (composePoint_w G later earlier h_over h_comp)).left := sorry

/-- The composite arrow point `(u₂, Z₂, z₁ ∘ z₂)` of a composable pair. -/
private def composePoint (G : GroupoidAlgebraicSpace B) {T : Over S}
    (later earlier : ArrowPoint G T)
    (h_over : later.a ≫ G.U.hom = earlier.a ≫ G.U.hom)
    (h_comp : later.z ≫ G.s.left = earlier.z ≫ G.t.left)
    (h_family : later.toWithSection = targetPoint G earlier) : ArrowPoint G T where
  toWithSection := earlier.toWithSection
  z :=
    (G.compose
        (zOverAs G later (pointToB G earlier)
          (composePoint_over G later earlier h_over))
        (zOver G earlier) (composePoint_w G later earlier h_over h_comp)).left
  z_source := by
    have hc := congrArg (fun f ↦ f.left)
      (G.compose_source
        (zOverAs G later (pointToB G earlier) (composePoint_over G later earlier h_over))
        (zOver G earlier) (composePoint_w G later earlier h_over h_comp))
    exact hc.trans earlier.z_source
  factors_z := composePoint_factors_z G later earlier h_over h_comp h_family

private theorem ArrowPoint.restrict_factors_z (G : GroupoidAlgebraicSpace B)
    {T T' : Over S} (p : ArrowPoint G T) (h : T' ⟶ T) :
    ∃ ℓ : ofOver T' ⟶ (OpenSubspace.fromOpens (p.toWithSection.restrict h).Z).X,
      ℓ ≫ (OpenSubspace.fromOpens (p.toWithSection.restrict h).Z).ι ≫
          pullback.fst (ofOverMap h ≫ p.a) G.s.left = 𝟙 (ofOver T') ∧
        ℓ ≫ (OpenSubspace.fromOpens (p.toWithSection.restrict h).Z).ι ≫
          pullback.snd (ofOverMap h ≫ p.a) G.s.left = ofOverMap h ≫ p.z := sorry

/-- Base change of an arrow point along `h : T' ⟶ T`. -/
@[no_expose]
def ArrowPoint.restrict (G : GroupoidAlgebraicSpace B) {T T' : Over S}
    (p : ArrowPoint G T) (h : T' ⟶ T) : ArrowPoint G T' where
  toWithSection := p.toWithSection.restrict h
  z := ofOverMap h ≫ p.z
  z_source := by
    change (ofOverMap h ≫ p.z) ≫ G.s.left = ofOverMap h ≫ p.a
    rw [Category.assoc, p.z_source]
  factors_z := ArrowPoint.restrict_factors_z G p h

private theorem ArrowPoint.restrict_id (G : GroupoidAlgebraicSpace B) {T : Over S}
    (p : ArrowPoint G T) : p.restrict G (𝟙 T) = p := sorry

private theorem ArrowPoint.restrict_comp (G : GroupoidAlgebraicSpace B)
    {T T' T'' : Over S} (p : ArrowPoint G T) (h : T' ⟶ T) (k : T'' ⟶ T') :
    (p.restrict G h).restrict G k = p.restrict G (k ≫ h) := sorry

private theorem arrowPointSmall (G : GroupoidAlgebraicSpace B) (T : Over S) :
    Small.{u} (ArrowPoint G T) := by
  apply small_of_injective (f := fun p : ArrowPoint G T ↦
    ((FinitePart.withSectionFunctor_obj_equiv G.s.left G.e.left
      (unit_source_left G) T).symm p.toWithSection,
      yonedaEquiv (p.z : yoneda.obj T ⟶ G.R.left.functorOfPoints)))
  intro p q h
  have hp : p.toWithSection = q.toWithSection :=
    (FinitePart.withSectionFunctor_obj_equiv G.s.left G.e.left
      (unit_source_left G) T).symm.injective (congrArg Prod.fst h)
  have hz : p.z = q.z := yonedaEquiv.injective (congrArg Prod.snd h)
  cases p
  cases q
  cases hp
  cases hz
  rfl

private def arrowPointModel (G : GroupoidAlgebraicSpace B) (T : Over S) : Type u :=
  @Shrink.{u, u + 1} (ArrowPoint G T) (arrowPointSmall G T)

private def arrowPointModelEquiv (G : GroupoidAlgebraicSpace B) (T : Over S) :
    ArrowPoint G T ≃ arrowPointModel G T :=
  @equivShrink.{u, u + 1} (ArrowPoint G T) (arrowPointSmall G T)

variable (G : GroupoidAlgebraicSpace B)


/-- The functor of `T`-points of the universal finite subspace `Z_univ`. -/
@[no_expose]
def arrowFunctor : (Over S)ᵒᵖ ⥤ Type u where
  obj T := arrowPointModel G T.unop
  map {T T'} h :=
    TypeCat.ofHom fun p ↦
      arrowPointModelEquiv G T'.unop
        (ArrowPoint.restrict G ((arrowPointModelEquiv G T.unop).symm p) h.unop)
  map_id T := by
    apply ConcreteCategory.hom_ext
    intro p
    change arrowPointModelEquiv G T.unop
      (((arrowPointModelEquiv G T.unop).symm p).restrict G (𝟙 T.unop)) = p
    rw [ArrowPoint.restrict_id, Equiv.apply_symm_apply]
  map_comp h k := by
    apply ConcreteCategory.hom_ext
    intro p
    change arrowPointModelEquiv G _
      (((arrowPointModelEquiv G _).symm p).restrict G (k.unop ≫ h.unop)) =
      arrowPointModelEquiv G _
        (((arrowPointModelEquiv G _).symm (arrowPointModelEquiv G _
          (((arrowPointModelEquiv G _).symm p).restrict G h.unop))).restrict G k.unop)
    rw [Equiv.symm_apply_apply, ArrowPoint.restrict_comp]

/-- Values of the arrow functor are equivalent to arrow points. -/
@[no_expose]
def arrowFunctor_obj_equiv (T : Over S) :
    (arrowFunctor G).obj (op T) ≃ ArrowPoint G T :=
  (arrowPointModelEquiv G T).symm

variable [AlgebraicSpace.Separated G.s.left] [AlgebraicSpace.LocallyOfFiniteType G.s.left]
variable [AlgebraicSpace.Separated G.t.left] [AlgebraicSpace.LocallyOfFiniteType G.t.left]

private theorem univSpace_isSheaf (G : GroupoidAlgebraicSpace B)
    [AlgebraicSpace.Separated G.s.left] [AlgebraicSpace.LocallyOfFiniteType G.s.left]
    [AlgebraicSpace.Separated G.t.left] [AlgebraicSpace.LocallyOfFiniteType G.t.left] :
    Presheaf.IsSheaf (Scheme.fppfTopology.over S) (arrowFunctor G) := sorry

private theorem univSpace_representableDiagonal (G : GroupoidAlgebraicSpace B)
    [AlgebraicSpace.Separated G.s.left] [AlgebraicSpace.LocallyOfFiniteType G.s.left]
    [AlgebraicSpace.Separated G.t.left] [AlgebraicSpace.LocallyOfFiniteType G.t.left] :
    yoneda.relativelyRepresentable (Limits.diag (arrowFunctor G)) := sorry

private theorem univSpace_atlas (G : GroupoidAlgebraicSpace B)
    [AlgebraicSpace.Separated G.s.left] [AlgebraicSpace.LocallyOfFiniteType G.s.left]
    [AlgebraicSpace.Separated G.t.left] [AlgebraicSpace.LocallyOfFiniteType G.t.left] :
    ∃ (U : Over S) (p : yoneda.obj U ⟶ arrowFunctor G),
      MorphismProperty.presheaf (MorphismProperty.over (@AlgebraicGeometry.Etale)) p ∧
        Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) p := sorry

/-- The algebraic space underlying `Z_univ`. -/
def univSpace : AlgebraicSpace S :=
  ofFunctor (arrowFunctor G) (by exact univSpace_isSheaf G)
    (by exact univSpace_representableDiagonal G) (by exact univSpace_atlas G)

/-- The functor of points of `univSpace G` is the arrow functor. -/
theorem univSpace_functorOfPoints : (univSpace G).functorOfPoints = arrowFunctor G := by
  exact ofFunctor_functorOfPoints _ _ _ _

/-- The morphism `g : U' ⟶ U` from the finite-part-with-section space of `G.s`. -/
def finitePartToU :
    FinitePart.withSectionSpace G.s.left G.e.left (unit_source_left G) ⟶ G.U.left :=
  FinitePart.withSectionToY G.s.left G.e.left (unit_source_left G)

/-- Recover a with-section pair from a morphism into the with-section space. -/
private def withSectionOfHom {T : Over S}
    (f : ofOver T ⟶
      FinitePart.withSectionSpace G.s.left G.e.left (unit_source_left G)) :
    FinitePart.WithSection.Point G.s.left G.e.left (unit_source_left G) T :=
  (FinitePart.withSectionFunctor_obj_equiv G.s.left G.e.left (unit_source_left G) T)
    (yonedaEquiv
      (f :
        yoneda.obj T ⟶
          (FinitePart.withSectionSpace G.s.left G.e.left
              (unit_source_left G)).functorOfPoints))

/-- The classifying morphism of a with-section pair. -/
@[no_expose]
def withSectionHom {T : Over S}
    (p : FinitePart.WithSection.Point G.s.left G.e.left (unit_source_left G) T) :
    ofOver T ⟶ FinitePart.withSectionSpace G.s.left G.e.left (unit_source_left G) :=
  (yonedaEquiv.symm
      ((FinitePart.withSectionFunctor_obj_equiv G.s.left G.e.left (unit_source_left G) T).symm
          p) :
    ofOver T ⟶
      FinitePart.withSectionSpace G.s.left G.e.left (unit_source_left G))

/-- The classifying morphism of a with-section pair recovers the object map `a`. -/
theorem withSectionHom_toU {T : Over S}
    (p : FinitePart.WithSection.Point G.s.left G.e.left (unit_source_left G) T) :
    withSectionHom G p ≫ finitePartToU G = p.a := sorry

/-- Recover an arrow point from a morphism into `univSpace G`. -/
private def arrowPointOfHom {T : Over S} (f : ofOver T ⟶ univSpace G) : ArrowPoint G T :=
  (arrowPointModelEquiv G T).symm
    (yonedaEquiv (f : yoneda.obj T ⟶ (univSpace G).functorOfPoints))

/-- The two legs of an arrow point agree over `U`, inducing a map to the fibre product. -/
private theorem univιPoint_condition {T : Over S} (p : ArrowPoint G T) :
    withSectionHom G p.toWithSection ≫ finitePartToU G = p.z ≫ G.s.left := by
  rw [withSectionHom_toU]
  exact p.z_source.symm

/-- The map `T ⟶ U' ×_U R` associated to an arrow point. -/
private def univιPoint {T : Over S} (p : ArrowPoint G T) :
    ofOver T ⟶ pullback (finitePartToU G) G.s.left :=
  pullback.lift (withSectionHom G p.toWithSection) p.z (univιPoint_condition G p)

/-- A with-section pair and an arrow over `a` induce a map to `U' ×_U R`. -/
private theorem univPoint_condition {T : Over S}
    (p : FinitePart.WithSection.Point G.s.left G.e.left (unit_source_left G) T)
    (z : ofOver T ⟶ G.R.left) (hz : z ≫ G.s.left = p.a) :
    withSectionHom G p ≫ finitePartToU G = z ≫ G.s.left := by
  rw [withSectionHom_toU]
  exact hz.symm

/-- The `T`-point of `U' ×_U R` associated to a with-section pair and an arrow. -/
@[no_expose]
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
      withSectionHom G p := by
  exact pullback.lift_fst _ _ _

/-- The second projection of `univPoint G p z hz` is the arrow `z`. -/
theorem univPoint_snd {T : Over S}
    (p : FinitePart.WithSection.Point G.s.left G.e.left (unit_source_left G) T)
    (z : ofOver T ⟶ G.R.left) (hz : z ≫ G.s.left = p.a) :
    univPoint G p z hz ≫ pullback.snd (finitePartToU G) G.s.left = z := by
  exact pullback.lift_snd _ _ _

private def univιApp (T : (Over S)ᵒᵖ) :
    (univSpace G).functorOfPoints.obj T ⟶ (pullback (finitePartToU G) G.s.left).functorOfPoints.obj T :=
    TypeCat.ofHom fun p ↦
      yonedaEquiv
        (univιPoint G ((arrowPointModelEquiv G T.unop).symm p) :
          yoneda.obj T.unop ⟶ (pullback (finitePartToU G) G.s.left).functorOfPoints)

private theorem univι_naturality {T T' : (Over S)ᵒᵖ} (h : T ⟶ T') :
    (univSpace G).functorOfPoints.map h ≫ univιApp G T' =
      univιApp G T ≫ (pullback (finitePartToU G) G.s.left).functorOfPoints.map h := sorry

/-- The inclusion `Z_univ ⊂ U' ×_{g, U, s} R`. -/
@[no_expose]
def univι : univSpace G ⟶ pullback (finitePartToU G) G.s.left where
  app := univιApp G
  naturality {_ _} h := univι_naturality G h

/-- The graph of `z` factors through the open `p.Z ⊂ |T ×_U R|`. -/
@[no_expose]
def factorsThroughOpen {T : Over S}
    (p : FinitePart.WithSection.Point G.s.left G.e.left (unit_source_left G) T)
    (z : ofOver T ⟶ G.R.left) : Prop :=
  ∃ ℓ : ofOver T ⟶ (OpenSubspace.fromOpens p.Z).X,
    ℓ ≫ (OpenSubspace.fromOpens p.Z).ι ≫ pullback.fst p.a G.s.left = 𝟙 (ofOver T) ∧
      ℓ ≫ (OpenSubspace.fromOpens p.Z).ι ≫ pullback.snd p.a G.s.left = z

/-- A morphism into `U' ×_U R` factors through `Z_univ`. -/
@[no_expose]
def factorsThroughUnivι {T : Over S}
    (q : ofOver T ⟶ pullback (finitePartToU G) G.s.left) : Prop :=
  ∃ ℓ : ofOver T ⟶ univSpace G, ℓ ≫ univι G = q

private def sourceLeftApp (T : (Over S)ᵒᵖ) :
    (univSpace G).functorOfPoints.obj T ⟶ (FinitePart.withSectionSpace G.s.left G.e.left (unit_source_left G)).functorOfPoints.obj T :=
    TypeCat.ofHom fun p ↦
      (FinitePart.withSectionFunctor_obj_equiv G.s.left G.e.left (unit_source_left G) T.unop).symm
        ((arrowPointModelEquiv G T.unop).symm p).toWithSection

private theorem sourceLeft_naturality {T T' : (Over S)ᵒᵖ} (h : T ⟶ T') :
    (univSpace G).functorOfPoints.map h ≫ sourceLeftApp G T' =
      sourceLeftApp G T ≫ (FinitePart.withSectionSpace G.s.left G.e.left (unit_source_left G)).functorOfPoints.map h := sorry

/-- The forgetful map `Z_univ ⟶ U'` on underlying algebraic spaces. -/
@[no_expose]
def sourceLeft :
    univSpace G ⟶ FinitePart.withSectionSpace G.s.left G.e.left (unit_source_left G) where
  app := sourceLeftApp G
  naturality {_ _} h := sourceLeft_naturality G h

private def targetLeftApp (T : (Over S)ᵒᵖ) :
    (univSpace G).functorOfPoints.obj T ⟶ (FinitePart.withSectionSpace G.s.left G.e.left (unit_source_left G)).functorOfPoints.obj T :=
    TypeCat.ofHom fun p ↦
      (FinitePart.withSectionFunctor_obj_equiv G.s.left G.e.left (unit_source_left G) T.unop).symm
        (targetPoint G ((arrowPointModelEquiv G T.unop).symm p))

private theorem targetLeft_naturality {T T' : (Over S)ᵒᵖ} (h : T ⟶ T') :
    (univSpace G).functorOfPoints.map h ≫ targetLeftApp G T' =
      targetLeftApp G T ≫ (FinitePart.withSectionSpace G.s.left G.e.left (unit_source_left G)).functorOfPoints.map h := sorry

/-- The target map `Z_univ ⟶ U'` on underlying algebraic spaces. -/
@[no_expose]
def targetLeft :
    univSpace G ⟶ FinitePart.withSectionSpace G.s.left G.e.left (unit_source_left G) where
  app := targetLeftApp G
  naturality {_ _} h := targetLeft_naturality G h

private def unitLeftApp (T : (Over S)ᵒᵖ) :
    (FinitePart.withSectionSpace G.s.left G.e.left (unit_source_left G)).functorOfPoints.obj T ⟶ (univSpace G).functorOfPoints.obj T :=
    TypeCat.ofHom fun p ↦
      arrowPointModelEquiv G T.unop
        (unitPoint G
          ((FinitePart.withSectionFunctor_obj_equiv G.s.left G.e.left (unit_source_left G) T.unop)
            p))

private theorem unitLeft_naturality {T T' : (Over S)ᵒᵖ} (h : T ⟶ T') :
    (FinitePart.withSectionSpace G.s.left G.e.left (unit_source_left G)).functorOfPoints.map h ≫ unitLeftApp G T' =
      unitLeftApp G T ≫ (univSpace G).functorOfPoints.map h := sorry

/-- The identity-arrow map `U' ⟶ Z_univ` on underlying algebraic spaces. -/
@[no_expose]
def unitLeft :
    FinitePart.withSectionSpace G.s.left G.e.left (unit_source_left G) ⟶ univSpace G where
  app := unitLeftApp G
  naturality {_ _} h := unitLeft_naturality G h

private def inverseLeftApp (T : (Over S)ᵒᵖ) :
    (univSpace G).functorOfPoints.obj T ⟶ (univSpace G).functorOfPoints.obj T :=
    TypeCat.ofHom fun p ↦
      arrowPointModelEquiv G T.unop
        (inversePoint G ((arrowPointModelEquiv G T.unop).symm p))

private theorem inverseLeft_naturality {T T' : (Over S)ᵒᵖ} (h : T ⟶ T') :
    (univSpace G).functorOfPoints.map h ≫ inverseLeftApp G T' =
      inverseLeftApp G T ≫ (univSpace G).functorOfPoints.map h := sorry

/-- The inverse-arrow map of `Z_univ` on underlying algebraic spaces. -/
@[no_expose]
def inverseLeft : univSpace G ⟶ univSpace G where
  app := inverseLeftApp G
  naturality {_ _} h := inverseLeft_naturality G h

/-- The arrow map `Z_univ ⟶ R` sending `(u, Z, z)` to `z`. -/
@[no_expose]
def univToR : univSpace G ⟶ G.R.left :=
  univι G ≫ pullback.snd (finitePartToU G) G.s.left

/-- The structure morphism of `Z_univ` over `B`. -/
private def univToB : univSpace G ⟶ B :=
  univToR G ≫ G.R.hom

/-- The object space `U'` of the finite-part groupoid, as an object over `B`. -/
def finitePartObject : Over B :=
  Over.mk (finitePartToU G ≫ G.U.hom)

/-- The arrow space `Z_univ` of the finite-part groupoid, as an object over `B`. -/
def finitePartArrow : Over B :=
  Over.mk (univToR G ≫ G.R.hom)

/-- The source map of the finite-part groupoid lies over `B`. -/
private theorem finitePart_s_w : sourceLeft G ≫ (finitePartObject G).hom = (finitePartArrow G).hom :=
  sorry

/-- The source map `s' : Z_univ ⟶ U'`. -/
@[no_expose]
def finitePart_s : finitePartArrow G ⟶ finitePartObject G :=
  Over.homMk (sourceLeft G) (finitePart_s_w G)

/-- The target map of the finite-part groupoid lies over `B`. -/
private theorem finitePart_t_w : targetLeft G ≫ (finitePartObject G).hom = (finitePartArrow G).hom :=
  sorry

/-- The target map `t' : Z_univ ⟶ U'`. -/
@[no_expose]
def finitePart_t : finitePartArrow G ⟶ finitePartObject G :=
  Over.homMk (targetLeft G) (finitePart_t_w G)

/-- The identity map of the finite-part groupoid lies over `B`. -/
private theorem finitePart_e_w : unitLeft G ≫ (finitePartArrow G).hom = (finitePartObject G).hom :=
  sorry

/-- The identity-arrow map `e' : U' ⟶ Z_univ`. -/
@[no_expose]
def finitePart_e : finitePartObject G ⟶ finitePartArrow G :=
  Over.homMk (unitLeft G) (finitePart_e_w G)

/-- The inverse map of the finite-part groupoid lies over `B`. -/
private theorem finitePart_i_w : inverseLeft G ≫ (finitePartArrow G).hom = (finitePartArrow G).hom :=
  sorry

/-- The inverse-arrow map `i' : Z_univ ⟶ Z_univ`. -/
@[no_expose]
def finitePart_i : finitePartArrow G ⟶ finitePartArrow G :=
  Over.homMk (inverseLeft G) (finitePart_i_w G)

/-- The later arrow point of a morphism into the composable-arrow pullback. -/
private def laterPointOfHom {T : Over S}
    (f : ofOver T ⟶ (pullback (finitePart_s G) (finitePart_t G)).left) :
    ArrowPoint G T :=
  arrowPointOfHom G (f ≫ (pullback.fst (finitePart_s G) (finitePart_t G)).left)

/-- The earlier arrow point of a morphism into the composable-arrow pullback. -/
private def earlierPointOfHom {T : Over S}
    (f : ofOver T ⟶ (pullback (finitePart_s G) (finitePart_t G)).left) :
    ArrowPoint G T :=
  arrowPointOfHom G (f ≫ (pullback.snd (finitePart_s G) (finitePart_t G)).left)

/-- Composable finite-part arrows lie over the same object of `B`. -/
private theorem laterPointOfHom_over {T : Over S}
    (f : ofOver T ⟶ (pullback (finitePart_s G) (finitePart_t G)).left) :
    (laterPointOfHom G f).a ≫ G.U.hom = (earlierPointOfHom G f).a ≫ G.U.hom :=
  sorry

/-- The later and earlier arrows of a composable pair of finite-part arrows
are composable. -/
private theorem laterPointOfHom_comp {T : Over S}
    (f : ofOver T ⟶ (pullback (finitePart_s G) (finitePart_t G)).left) :
    (laterPointOfHom G f).z ≫ G.s.left = (earlierPointOfHom G f).z ≫ G.t.left :=
  sorry

private theorem laterPointOfHom_target {T : Over S}
    (f : ofOver T ⟶ (pullback (finitePart_s G) (finitePart_t G)).left) :
    (laterPointOfHom G f).toWithSection = targetPoint G (earlierPointOfHom G f) := sorry

/-- The composite arrow point of a morphism into the composable-arrow pullback. -/
private def composePointOfHom {T : Over S}
    (f : ofOver T ⟶ (pullback (finitePart_s G) (finitePart_t G)).left) :
    ArrowPoint G T :=
  composePoint G (laterPointOfHom G f) (earlierPointOfHom G f)
    (laterPointOfHom_over G f) (laterPointOfHom_comp G f) (laterPointOfHom_target G f)

private def compositionLeftApp (T : (Over S)ᵒᵖ) :
    (pullback (finitePart_s G) (finitePart_t G)).left.functorOfPoints.obj T ⟶ (univSpace G).functorOfPoints.obj T :=
    TypeCat.ofHom fun φ ↦
      arrowPointModelEquiv G T.unop
        (composePointOfHom G
          (yonedaEquiv.symm φ :
            ofOver T.unop ⟶ (pullback (finitePart_s G) (finitePart_t G)).left))

private theorem compositionLeft_naturality {T T' : (Over S)ᵒᵖ} (h : T ⟶ T') :
    (pullback (finitePart_s G) (finitePart_t G)).left.functorOfPoints.map h ≫ compositionLeftApp G T' =
      compositionLeftApp G T ≫ (univSpace G).functorOfPoints.map h := sorry

/-- The composition map of the finite-part groupoid on underlying algebraic spaces. -/
@[no_expose]
def compositionLeft :
    (pullback (finitePart_s G) (finitePart_t G)).left ⟶ univSpace G where
  app := compositionLeftApp G
  naturality {_ _} h := compositionLeft_naturality G h

/-- The composition map of the finite-part groupoid lies over `B`. -/
private theorem finitePart_c_w :
    compositionLeft G ≫ (finitePartArrow G).hom =
      (pullback (finitePart_s G) (finitePart_t G)).hom := sorry

/-- The composition map `c'` of the finite-part groupoid. -/
@[no_expose]
def finitePart_c : pullback (finitePart_s G) (finitePart_t G) ⟶ finitePartArrow G :=
  Over.homMk (compositionLeft G) (finitePart_c_w G)

private theorem finitePart_comp_source :
    (finitePart_c G) ≫ (finitePart_s G) = pullback.snd (finitePart_s G) (finitePart_t G) ≫ (finitePart_s G) := sorry

private theorem finitePart_comp_target :
    (finitePart_c G) ≫ (finitePart_t G) = pullback.fst (finitePart_s G) (finitePart_t G) ≫ (finitePart_t G) := sorry

private theorem finitePart_identity_source :
    (finitePart_e G) ≫ (finitePart_s G) = 𝟙 (finitePartObject G) := sorry

private theorem finitePart_identity_target :
    (finitePart_e G) ≫ (finitePart_t G) = 𝟙 (finitePartObject G) := sorry

private theorem finitePart_inverse_source :
    (finitePart_i G) ≫ (finitePart_s G) = (finitePart_t G) := sorry

private theorem finitePart_inverse_target :
    (finitePart_i G) ≫ (finitePart_t G) = (finitePart_s G) := sorry

private theorem finitePart_associativity :
    ∀ {T : Over B} (a b d : T ⟶ (finitePartArrow G))
      (h_ab : a ≫ (finitePart_s G) = b ≫ (finitePart_t G)) (h_bd : b ≫ (finitePart_s G) = d ≫ (finitePart_t G))
      (h_ab_d : (pullback.lift a b h_ab ≫ (finitePart_c G)) ≫ (finitePart_s G) = d ≫ (finitePart_t G))
      (h_a_bd : a ≫ (finitePart_s G) = (pullback.lift b d h_bd ≫ (finitePart_c G)) ≫ (finitePart_t G)),
      pullback.lift (pullback.lift a b h_ab ≫ (finitePart_c G)) d h_ab_d ≫ (finitePart_c G) =
        pullback.lift a (pullback.lift b d h_bd ≫ (finitePart_c G)) h_a_bd ≫ (finitePart_c G) := sorry

private theorem finitePart_right_identity :
    ∀ {T : Over B} (a : T ⟶ (finitePartArrow G))
      (h : a ≫ (finitePart_s G) = ((a ≫ (finitePart_s G)) ≫ (finitePart_e G)) ≫ (finitePart_t G)),
      pullback.lift a ((a ≫ (finitePart_s G)) ≫ (finitePart_e G)) h ≫ (finitePart_c G) = a := sorry

private theorem finitePart_left_identity :
    ∀ {T : Over B} (a : T ⟶ (finitePartArrow G))
      (h : ((a ≫ (finitePart_t G)) ≫ (finitePart_e G)) ≫ (finitePart_s G) = a ≫ (finitePart_t G)),
      pullback.lift ((a ≫ (finitePart_t G)) ≫ (finitePart_e G)) a h ≫ (finitePart_c G) = a := sorry

private theorem finitePart_inverse_comp :
    ∀ {T : Over B} (a : T ⟶ (finitePartArrow G))
      (h : a ≫ (finitePart_s G) = (a ≫ (finitePart_i G)) ≫ (finitePart_t G)),
      pullback.lift a (a ≫ (finitePart_i G)) h ≫ (finitePart_c G) = (a ≫ (finitePart_t G)) ≫ (finitePart_e G) := sorry

private theorem finitePart_comp_inverse :
    ∀ {T : Over B} (a : T ⟶ (finitePartArrow G))
      (h : (a ≫ (finitePart_i G)) ≫ (finitePart_s G) = a ≫ (finitePart_t G)),
      pullback.lift (a ≫ (finitePart_i G)) a h ≫ (finitePart_c G) = (a ≫ (finitePart_s G)) ≫ (finitePart_e G) := sorry


/-- The finite-part groupoid of a groupoid in algebraic spaces over `B`. -/
def finitePart : GroupoidAlgebraicSpace B where
  U := finitePartObject G
  R := finitePartArrow G
  s := finitePart_s G
  t := finitePart_t G
  c := finitePart_c G
  e := finitePart_e G
  i := finitePart_i G
  comp_source := by exact finitePart_comp_source G
  comp_target := by exact finitePart_comp_target G
  identity_source := by exact finitePart_identity_source G
  identity_target := by exact finitePart_identity_target G
  inverse_source := by exact finitePart_inverse_source G
  inverse_target := by exact finitePart_inverse_target G
  associativity := by exact finitePart_associativity G
  right_identity := by exact finitePart_right_identity G
  left_identity := by exact finitePart_left_identity G
  inverse_comp := by exact finitePart_inverse_comp G
  comp_inverse := by exact finitePart_comp_inverse G

/-- The object space of the finite-part groupoid is the with-section finite-part space. -/
theorem finitePart_U :
    (finitePart G).U.left =
      FinitePart.withSectionSpace G.s.left G.e.left (unit_source_left G) := rfl

/-- The arrow space of the finite-part groupoid is `univSpace G`. -/
theorem finitePart_R : (finitePart G).R.left = univSpace G := rfl

/-- The object component of the canonical morphism lies over `B`. -/
private theorem finitePartHom_obj_w :
    finitePartToU G ≫ G.U.hom = (finitePart G).U.hom := rfl

/-- The arrow component of the canonical morphism lies over `B`. -/
private theorem finitePartHom_arrow_w : univToR G ≫ G.R.hom = (finitePart G).R.hom := rfl

private theorem finitePartHom_map_s :
    (finitePart G).s ≫ (Over.homMk (finitePartToU G) (by exact finitePartHom_obj_w G)) = (Over.homMk (univToR G) (by exact finitePartHom_arrow_w G)) ≫ G.s := sorry

private theorem finitePartHom_map_t :
    (finitePart G).t ≫ (Over.homMk (finitePartToU G) (by exact finitePartHom_obj_w G)) = (Over.homMk (univToR G) (by exact finitePartHom_arrow_w G)) ≫ G.t := sorry

private theorem finitePartHom_map_c :
    (finitePart G).c ≫ (Over.homMk (univToR G) (by exact finitePartHom_arrow_w G)) =
      composableMap (Over.homMk (finitePartToU G) (by exact finitePartHom_obj_w G)) (Over.homMk (univToR G) (by exact finitePartHom_arrow_w G)) (finitePartHom_map_s G) (finitePartHom_map_t G) ≫ G.c := sorry

/-- The canonical morphism from the finite-part groupoid to `G`. -/
def finitePartHom : Hom (finitePart G) G where
  obj := Over.homMk (finitePartToU G) (by exact finitePartHom_obj_w G)
  arrow := Over.homMk (univToR G) (by exact finitePartHom_arrow_w G)
  map_s := by exact finitePartHom_map_s G
  map_t := by exact finitePartHom_map_t G
  map_c := by exact finitePartHom_map_c G

/-- The object map of `finitePartHom G` is `g : U' ⟶ U`. -/
theorem finitePartHom_obj_left :
    (finitePartHom G).obj.left = finitePartToU G := rfl

/-- The arrow map of `finitePartHom G` sends `(u, Z, z)` to `z`. -/
theorem finitePartHom_arrow_left : (finitePartHom G).arrow.left = univToR G := rfl

/-- The morphism `g : U' ⟶ U` is étale. -/
theorem etale_finitePartHom_obj : AlgebraicSpace.Etale (finitePartHom G).obj.left := by
  exact FinitePart.etale_withSectionToY G.s.left G.e.left (unit_source_left G)

/-- The graph of the base change of `e` along `g`. -/
private theorem unitBaseChange_condition (G : GroupoidAlgebraicSpace B)
    [AlgebraicSpace.Separated G.s.left] [AlgebraicSpace.LocallyOfFiniteType G.s.left] :
    𝟙 (FinitePart.withSectionSpace G.s.left G.e.left (unit_source_left G)) ≫
        finitePartToU G =
      (finitePartToU G ≫ G.e.left) ≫ G.s.left := by
  simp only [Category.id_comp, Category.assoc, unit_source_left, Category.comp_id]

/-- The base change of the unit `e` along `g : U' ⟶ U`. -/
@[no_expose]
def unitBaseChange :
    FinitePart.withSectionSpace G.s.left G.e.left (unit_source_left G) ⟶
      pullback (finitePartToU G) G.s.left :=
  pullback.lift (𝟙 _) (finitePartToU G ≫ G.e.left) (unitBaseChange_condition G)

/-- The base change of `e` factors through `Z_univ`. -/
theorem unitBaseChange_factors : unitLeft G ≫ univι G = unitBaseChange G := sorry

/-- The object map `g : U' ⟶ U` of the canonical morphism is
identified with `(R_s / U, e)_fin ⟶ U`. -/
theorem finitePartHom_obj (G : GroupoidAlgebraicSpace B)
    [AlgebraicSpace.Separated G.s.left] [AlgebraicSpace.LocallyOfFiniteType G.s.left]
    [AlgebraicSpace.Separated G.t.left] [AlgebraicSpace.LocallyOfFiniteType G.t.left] :
    (finitePartHom G).obj.left =
      FinitePart.withSectionToY G.s.left G.e.left (unit_source_left G) := rfl

/-- `univι G` is an open immersion into
`pullback (finitePartHom G).obj.left G.s.left`. -/
theorem isOpenImmersion_univι (G : GroupoidAlgebraicSpace B)
    [AlgebraicSpace.Separated G.s.left] [AlgebraicSpace.LocallyOfFiniteType G.s.left]
    [AlgebraicSpace.Separated G.t.left] [AlgebraicSpace.LocallyOfFiniteType G.t.left] :
    AlgebraicSpace.IsOpenImmersion (univι G) := sorry

/-- `univι G` is a closed immersion into
`pullback (finitePartHom G).obj.left G.s.left`. -/
theorem isClosedImmersion_univι (G : GroupoidAlgebraicSpace B)
    [AlgebraicSpace.Separated G.s.left] [AlgebraicSpace.LocallyOfFiniteType G.s.left]
    [AlgebraicSpace.Separated G.t.left] [AlgebraicSpace.LocallyOfFiniteType G.t.left] :
    AlgebraicSpace.IsClosedImmersion (univι G) := sorry

/-- The projection `Z_univ ⟶ U'` is finite. -/
theorem isFinite_univPr (G : GroupoidAlgebraicSpace B)
    [AlgebraicSpace.Separated G.s.left] [AlgebraicSpace.LocallyOfFiniteType G.s.left]
    [AlgebraicSpace.Separated G.t.left] [AlgebraicSpace.LocallyOfFiniteType G.t.left] :
    AlgebraicSpace.IsFinite
      (univι G ≫ pullback.fst (finitePartHom G).obj.left G.s.left) := sorry

/-- An arrow lies in a classified finite family precisely when its classifying point
factors through the universal inclusion. -/
theorem univPoint_factors_iff {T : Over S}
    (p : FinitePart.WithSection.Point G.s.left G.e.left (unit_source_left G) T)
    (z : ofOver T ⟶ G.R.left) (hz : z ≫ G.s.left = p.a) :
    factorsThroughOpen G p z ↔ factorsThroughUnivι G (univPoint G p z hz) := sorry

/-- `Z_univ` contains the base change of the unit `e`, and is
the universal such family: an arrow `z` through a with-section pair `p` factors
through `p.Z` if and only if the corresponding point of
`pullback (finitePartHom G).obj.left G.s.left` factors through `univι G`. -/
theorem finitePartHom_univ (G : GroupoidAlgebraicSpace B)
    [AlgebraicSpace.Separated G.s.left] [AlgebraicSpace.LocallyOfFiniteType G.s.left]
    [AlgebraicSpace.Separated G.t.left] [AlgebraicSpace.LocallyOfFiniteType G.t.left] :
    unitLeft G ≫ univι G = unitBaseChange G ∧
      ∀ {T : Over S}
        (p : FinitePart.WithSection.Point G.s.left G.e.left (unit_source_left G) T)
        (z : ofOver T ⟶ G.R.left) (hz : z ≫ G.s.left = p.a),
        factorsThroughOpen G p z ↔
          factorsThroughUnivι G (univPoint G p z hz) := by
  exact ⟨unitBaseChange_factors G, fun p z hz ↦ univPoint_factors_iff G p z hz⟩

/-- The canonical finite-part groupoid morphism has the with-section object map and
universal arrow map. Its object map is étale, and its universal family is open,
closed, finite over the object space, contains the unit, and classifies membership
in every finite family containing the unit. -/
theorem finitePart_spec :
    (finitePartHom G).obj.left =
        FinitePart.withSectionToY G.s.left G.e.left (unit_source_left G) ∧
      (finitePartHom G).arrow.left = univToR G ∧
      AlgebraicSpace.Etale (finitePartHom G).obj.left ∧
      AlgebraicSpace.IsOpenImmersion (univι G) ∧
      AlgebraicSpace.IsClosedImmersion (univι G) ∧
      AlgebraicSpace.IsFinite
        (univι G ≫ pullback.fst (finitePartHom G).obj.left G.s.left) ∧
      unitLeft G ≫ univι G = unitBaseChange G ∧
      ∀ {T : Over S}
        (p : FinitePart.WithSection.Point G.s.left G.e.left (unit_source_left G) T)
        (z : ofOver T ⟶ G.R.left) (hz : z ≫ G.s.left = p.a),
        factorsThroughOpen G p z ↔ factorsThroughUnivι G (univPoint G p z hz) := by
  exact ⟨finitePartHom_obj G, finitePartHom_arrow_left G,
    etale_finitePartHom_obj G, isOpenImmersion_univι G,
    isClosedImmersion_univι G, isFinite_univPr G, finitePartHom_univ G⟩

end AlgebraicGeometry.GroupoidAlgebraicSpace

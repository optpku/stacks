module

public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import Mathlib.CategoryTheory.FiberedCategory.Fibered
public import ReasLib.AlgebraicGeometry.FormalDeformation.Completion
public import ReasLib.AlgebraicGeometry.FormalDeformation.Filtration

/-!
# Formal objects along a general maximal-adic equivalent filtration

Objects of `hat F_I(R)` are sequential inverse systems in `F` lying over the
truncations `R ⧸ I n`. Morphisms are stagewise maps lying over identities.
-/

@[expose] public section

open CategoryTheory IsLocalRing Opposite

universe u v

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{v} F]

namespace FormalObject

open CompleteLocalAlgCat

/-- A formal object of `p` along a filtration `I` of a fixed complete local algebra
`R` is a sequential inverse system in `F` lying over the truncations `R ⧸ I n`. -/
structure Along (p : F ⥤ ArtinianLocalAlgCat Λ k) (R : CompleteLocalAlgCat Λ k)
    (I : AdicIdealFiltration R) where
  /-- Inverse system of objects of `F` over the `I`-truncations of `R`. -/
  system : SequentialInverseSystem F
  /-- Stage `n` of the system lies over the `n`th `I`-truncation of `R`. -/
  over_obj : ∀ n : ℕ, p.obj (system.family n) = I.truncation n
  /-- The successor transition lies over the `I`-truncation projection. -/
  over_step : ∀ n : ℕ, p.IsHomLift (I.truncationMap n) (system.stepMap n)

namespace Along

variable {p : F ⥤ ArtinianLocalAlgCat Λ k} {R : CompleteLocalAlgCat Λ k}
  {I : AdicIdealFiltration R}

/-- Package a compatible inverse system over the `I`-truncations of `R`. -/
noncomputable def of (ξ : ℕ → F) (f : ∀ n, ξ (n + 1) ⟶ ξ n)
    (over_obj : ∀ n, p.obj (ξ n) = I.truncation n)
    (over_step : ∀ n, p.IsHomLift (I.truncationMap n) (f n)) :
    Along p R I where
  system := Functor.ofOpSequence f
  over_obj := over_obj
  over_step := sorry

/-- Stagewise specification of a formal object along `I`. -/
theorem spec (ξ : Along p R I) (n : ℕ) :
    p.obj (ξ.system.family n) = I.truncation n ∧
      p.IsHomLift (I.truncationMap n) (ξ.system.stepMap n) := sorry

/-- A morphism of formal objects along `I` is a natural family of morphisms of `F`
lying over identities of the `I`-truncations. -/
structure Hom (ξ η : Along p R I) where
  /-- Stagewise morphisms of the inverse systems. -/
  app : ∀ n : ℕ, ξ.system.family n ⟶ η.system.family n
  /-- Each stage of `app` lies over the identity of the corresponding truncation. -/
  over : ∀ n : ℕ, p.IsHomLift (𝟙 (I.truncation n)) (app n)
  /-- The stagewise maps intertwine successor transitions. -/
  naturality : ∀ n : ℕ,
    ξ.system.stepMap n ≫ app n = app (n + 1) ≫ η.system.stepMap n

/-- Identity morphism of a formal object along `I`. -/
def Hom.id (ξ : Along p R I) : Hom ξ ξ where
  app := fun n ↦ 𝟙 (ξ.system.family n)
  over := sorry
  naturality := sorry

/-- Composition of morphisms of formal objects along `I`. -/
def Hom.comp {ξ η ζ : Along p R I} (a : Hom ξ η) (b : Hom η ζ) : Hom ξ ζ where
  app := fun n ↦ a.app n ≫ b.app n
  over := sorry
  naturality := sorry

/-- A morphism of formal objects along `I` lies over identities and commutes with
successor transitions. -/
theorem Hom.spec {ξ η : Along p R I} (a : Hom ξ η) (n : ℕ) :
    p.IsHomLift (𝟙 (I.truncation n)) (a.app n) ∧
      ξ.system.stepMap n ≫ a.app n = a.app (n + 1) ≫ η.system.stepMap n := sorry

/-- The identity morphism has identity stage maps. -/
theorem Hom.id_app (ξ : Along p R I) (n : ℕ) :
    (Hom.id ξ).app n = 𝟙 (ξ.system.family n) := sorry

/-- Composition of morphisms along `I` composes stage maps. -/
theorem Hom.comp_app {ξ η ζ : Along p R I} (a : Hom ξ η) (b : Hom η ζ) (n : ℕ) :
    (Hom.comp a b).app n = a.app n ≫ b.app n := sorry

/-- Category of formal objects of `p` along a filtration `I` of `R`. -/
def category : Category.{v} (Along p R I) where
  Hom := Along.Hom
  id := Along.Hom.id
  comp := Along.Hom.comp
  id_comp := sorry
  comp_id := sorry
  assoc := sorry

variable [Functor.IsFibered.InGroupoids p.op]

/-- Hom-lifts of `p` reverse to hom-lifts of `p.op`. -/
@[reducible]
def isHomLift_op {S T : ArtinianLocalAlgCat Λ k} {a b : F} {f : S ⟶ T}
    {φ : a ⟶ b} (h : p.IsHomLift f φ) : p.op.IsHomLift (Quiver.Hom.op f) (Quiver.Hom.op φ) :=
  h.casesOn fun φ ↦ IsHomLift.map (p := p.op) (Quiver.Hom.op φ)

/-- Pushforward of an object of `F` along a morphism of `C_Λ`, obtained as a cartesian
lift for `p.op`. -/
noncomputable def pushforwardObj {a : F} {S T : ArtinianLocalAlgCat Λ k}
    (ha : p.obj a = S) (f : S ⟶ T) : F :=
  Opposite.unop (Functor.IsPreFibered.pullbackObj (p := p.op)
    (a := Opposite.op a) (ha := congrArg Opposite.op ha) (Quiver.Hom.op f))

/-- The cofibered pushforward morphism lying over `f`. -/
noncomputable def pushforwardMap {a : F} {S T : ArtinianLocalAlgCat Λ k}
    (ha : p.obj a = S) (f : S ⟶ T) : a ⟶ pushforwardObj ha f :=
  Quiver.Hom.unop (Functor.IsPreFibered.pullbackMap (p := p.op)
    (a := Opposite.op a) (ha := congrArg Opposite.op ha) (Quiver.Hom.op f))

/-- Composite of `k` successor transitions from stage `i + k` down to stage `i`. -/
def iterateStep (ξ : Along p R I) :
    ∀ (i k : ℕ), ξ.system.family (i + k) ⟶ ξ.system.family i
  | i, 0 => 𝟙 (ξ.system.family (i + 0))
  | i, k + 1 => ξ.system.stepMap (i + k) ≫ iterateStep ξ i k

/-- Transition from the least cofinal stage for `n + 1` down to that for `n`. -/
noncomputable def stageTransition (ξ : Along p R I) (n : ℕ) :
    ξ.system.family (I.stageIndex (n + 1)) ⟶ ξ.system.family (I.stageIndex n) :=
  eqToHom (congrArg ξ.system.family (Nat.add_sub_of_le (I.stageIndex_mono n)).symm) ≫
    iterateStep ξ (I.stageIndex n) (I.stageIndex (n + 1) - I.stageIndex n)

/-- The reindexed object `η_n` obtained by pushing `ξ_{m(n)}` along the comparison
`R ⧸ I_{m(n)} ⟶ R ⧸ m^{n+1}`. -/
noncomputable def reindexedObj (ξ : Along p R I) (n : ℕ) : F :=
  pushforwardObj (ξ.over_obj (I.stageIndex n)) (I.truncationComparison n)

/-- The unique lift of a cartesian morphism in `p.op`, viewed in `F`. -/
noncomputable def cartesianUnop {R S : (ArtinianLocalAlgCat Λ k)ᵒᵖ}
    {x y z : Fᵒᵖ} (f : R ⟶ S) (φ : y ⟶ x) (φ' : z ⟶ x)
    (hφ : p.op.IsCartesian f φ) (hφ' : p.op.IsHomLift f φ') :
    Opposite.unop y ⟶ Opposite.unop z :=
  Quiver.Hom.unop
    (@Functor.IsCartesian.map (ArtinianLocalAlgCat Λ k)ᵒᵖ Fᵒᵖ
      inferInstance inferInstance p.op R S y x f φ hφ z φ' hφ' :
      (Opposite.unop y ⟶ Opposite.unop z)ᵒᵖ)

/-- The unique strongly cartesian lift in `p.op`, viewed in `F`. -/
noncomputable def stronglyCartesianUnop {R S R' : (ArtinianLocalAlgCat Λ k)ᵒᵖ}
    {x y z : Fᵒᵖ} (f : R ⟶ S) (φ : y ⟶ x) (g : R' ⟶ R) (f' : R' ⟶ S)
    (hf' : f' = g ≫ f) (φ' : z ⟶ x)
    (hφ : p.op.IsStronglyCartesian f φ) (hφ' : p.op.IsHomLift f' φ') :
    Opposite.unop y ⟶ Opposite.unop z :=
  Quiver.Hom.unop
    (@Functor.IsStronglyCartesian.map (ArtinianLocalAlgCat Λ k)ᵒᵖ Fᵒᵖ
      inferInstance inferInstance p.op R S y x f φ hφ R' z g f' hf' φ' hφ' :
      (Opposite.unop y ⟶ Opposite.unop z)ᵒᵖ)

/-- Successor map of the pushed inverse system, obtained from the strongly cartesian
lift of the comparison at stage `n + 1`. -/
noncomputable def reindexedStep (ξ : Along p R I) (n : ℕ) :
    reindexedObj ξ (n + 1) ⟶ reindexedObj ξ n :=
  let φ := Functor.IsPreFibered.pullbackMap (p := p.op)
    (a := Opposite.op (ξ.system.family (I.stageIndex (n + 1))))
    (ha := congrArg Opposite.op (ξ.over_obj (I.stageIndex (n + 1))))
    (Quiver.Hom.op (I.truncationComparison (n + 1)))
  let φ' := Functor.IsPreFibered.pullbackMap (p := p.op)
      (a := Opposite.op (ξ.system.family (I.stageIndex n)))
      (ha := congrArg Opposite.op (ξ.over_obj (I.stageIndex n)))
      (Quiver.Hom.op (I.truncationComparison n)) ≫
    Quiver.Hom.op (ξ.stageTransition n)
  let g := eqToHom (Functor.IsPreFibered.pullbackObj_proj (p := p.op)
      (a := Opposite.op (ξ.system.family (I.stageIndex n)))
      (ha := congrArg Opposite.op (ξ.over_obj (I.stageIndex n)))
      (Quiver.Hom.op (I.truncationComparison n))) ≫
    Quiver.Hom.op (R.truncationMap n)
  let f := Quiver.Hom.op (I.truncationComparison (n + 1))
  stronglyCartesianUnop f φ g (g ≫ f) rfl φ' inferInstance
    (IsHomLift.of_fac p.op (g ≫ f) φ' rfl
      (congrArg Opposite.op (ξ.over_obj (I.stageIndex (n + 1)))) sorry)

/-- The formal object of `p` obtained by pushing an `I`-indexed system along the
maximal-adic comparisons. -/
noncomputable def toFormalObject (ξ : Along p R I) : FormalObject p :=
  FormalObject.of R (ξ.reindexedObj) (ξ.reindexedStep) (fun _ ↦ sorry) (fun _ ↦ sorry)

/-- Induced stage map of pushed systems along a morphism of `I`-indexed systems. -/
noncomputable def reindexedApp {ξ η : Along p R I} (a : Hom ξ η) (n : ℕ) :
    reindexedObj ξ n ⟶ reindexedObj η n :=
  let φ := Functor.IsPreFibered.pullbackMap (p := p.op)
    (a := Opposite.op (ξ.system.family (I.stageIndex n)))
    (ha := congrArg Opposite.op (ξ.over_obj (I.stageIndex n)))
    (Quiver.Hom.op (I.truncationComparison n))
  let φ' := Functor.IsPreFibered.pullbackMap (p := p.op)
      (a := Opposite.op (η.system.family (I.stageIndex n)))
      (ha := congrArg Opposite.op (η.over_obj (I.stageIndex n)))
      (Quiver.Hom.op (I.truncationComparison n)) ≫
    Quiver.Hom.op (a.app (I.stageIndex n))
  cartesianUnop (Quiver.Hom.op (I.truncationComparison n)) φ φ' inferInstance
    (@IsHomLift.comp_lift_id_right (ArtinianLocalAlgCat Λ k)ᵒᵖ Fᵒᵖ inferInstance inferInstance
      p.op _ _ _ _ _ (Quiver.Hom.op (I.truncationComparison n))
      (Functor.IsPreFibered.pullbackMap (p := p.op)
        (a := Opposite.op (η.system.family (I.stageIndex n)))
        (ha := congrArg Opposite.op (η.over_obj (I.stageIndex n)))
        (Quiver.Hom.op (I.truncationComparison n)))
      inferInstance (Quiver.Hom.op (a.app (I.stageIndex n)))
      (isHomLift_op (a.over (I.stageIndex n))))

/-- Underlying morphism of formal objects induced by a morphism along `I`. -/
noncomputable def toFormalObjectMap {ξ η : Along p R I} (a : Hom ξ η) :
    FormalObject.Hom ξ.toFormalObject η.toFormalObject :=
  FormalObject.Hom.of (𝟙 R) (fun n ↦ reindexedApp a n)
    (fun n ↦ 𝟙 (R.truncation n)) (fun _ ↦ sorry) (fun _ ↦ sorry) (fun _ ↦ sorry)

/-- The comparison functor `hat F_I(R) ⥤ hat F(R)` sending an inverse system over
`R ⧸ I n` to the pushed inverse system over the maximal-adic truncations of `R`. -/
noncomputable def toFiber (p : F ⥤ ArtinianLocalAlgCat Λ k)
    [Functor.IsFibered.InGroupoids p.op] (R : CompleteLocalAlgCat Λ k)
    (I : AdicIdealFiltration R) :
    -- Local instance justification (defeq pin): the functor source must use the explicit category with the specified Along.Hom operations.
    letI := category (p := p) (R := R) (I := I)
    Along p R I ⥤ Functor.Fiber (Functor.completion p) R :=
  -- Local instance justification (defeq pin): construct the functor using exactly the category fixed by its source type.
  letI := category (p := p) (R := R) (I := I)
  { obj ξ := ⟨toFormalObject ξ, rfl⟩
    map a := ⟨toFormalObjectMap a, sorry⟩
    map_id := sorry
    map_comp := sorry }

/-- The comparison functor sends an `I`-indexed system to the pushed formal object
over `R`. -/
theorem toFiber_obj (ξ : Along p R I) :
    -- Local instance justification (defeq pin): the object projection must use the source category stored in toFiber.
    letI := category (p := p) (R := R) (I := I)
    ((toFiber p R I).obj ξ).1 = toFormalObject ξ := sorry

/-- The comparison functor acts on morphisms by the induced maps of pushed systems. -/
theorem toFiber_map {ξ η : Along p R I} (a : Hom ξ η) :
    -- Local instance justification (defeq pin): the map projection must use the explicit Along.Hom category stored in toFiber.
    letI := category (p := p) (R := R) (I := I)
    Functor.Fiber.fiberInclusion.map ((toFiber p R I).map a) = toFormalObjectMap a := sorry

end Along

end FormalObject

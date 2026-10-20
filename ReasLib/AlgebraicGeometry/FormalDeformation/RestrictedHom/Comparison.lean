module

public import ReasLib.AlgebraicGeometry.FormalDeformation.RestrictedHom.Inverse
public import ReasLib.AlgebraicGeometry.FormalDeformation.Completion.Restriction
public import ReasLib.CategoryTheory.Cofibered.Pushforward

/-!
# Cofibered 2-Yoneda comparison for restricted coyoneda

Stagewise completion of a restricted coyoneda morphism followed by evaluation at
the identity agrees with evaluation on identity truncations. The cofibered Yoneda
section sends a formal object to its chosen pushforwards and agrees, up to
isomorphism, with completion of the nilpotency-pushforward functor.
-/

@[expose] public section

open CategoryTheory IsLocalRing Opposite ArtinianLocalAlgCat CompleteLocalAlgCat Functor
open scoped BasedFunctor

universe u v

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{v} F]

namespace FormalObject

noncomputable section

set_option backward.privateInPublic true

variable {p : F ⥤ ArtinianLocalAlgCat Λ k} [IsFibered.InGroupoids p.op]

/-- Identity-truncation stages of a morphism `f : R ⟶ S`, as objects of
`underline R |_{C_Λ}`. -/
private def phiRestrictedStage {R : CompleteLocalAlgCat Λ k}
    (x : (coyoneda.obj (op R)).Elements) (n : ℕ) :
    (restrictedCoyoneda R).Elements :=
  ⟨x.1.truncation n, x.2 ≫ truncationToInclusion x.1 n⟩

/-- Successor map of identity-truncation stages of `f : R ⟶ S`. -/
private def phiRestrictedStageMap {R : CompleteLocalAlgCat Λ k}
    (x : (coyoneda.obj (op R)).Elements) (n : ℕ) :
    phiRestrictedStage x (n + 1) ⟶ phiRestrictedStage x n :=
  CategoryOfElements.homMk (phiRestrictedStage x (n + 1)) (phiRestrictedStage x n)
    (x.1.truncationMap n) sorry

/-- Truncation of a complete local map, as a morphism of identity-truncation stages. -/
private def phiRestrictedStageHom {R : CompleteLocalAlgCat Λ k}
    {x y : (coyoneda.obj (op R)).Elements} (g : x ⟶ y) (n : ℕ) :
    phiRestrictedStage x n ⟶ phiRestrictedStage y n :=
  CategoryOfElements.homMk (phiRestrictedStage x n) (phiRestrictedStage y n)
    (truncationHom g.val n) sorry

/-- Formal object over `S` obtained by applying `φ` to the identity truncations of
`f : R ⟶ S`. -/
private def phiRestrictedObj {R : CompleteLocalAlgCat Λ k} (φ : RestrictedHom p R)
    (x : (coyoneda.obj (op R)).Elements) : FormalObject p :=
  FormalObject.of x.1 (fun n ↦ φ.obj (phiRestrictedStage x n))
    (fun n ↦ φ.map (phiRestrictedStageMap x n)) (fun _ ↦ sorry) (fun _ ↦ sorry)

/-- Stagewise action of `φ` on a morphism of `underline R`. -/
private def phiRestrictedHom {R : CompleteLocalAlgCat Λ k} (φ : RestrictedHom p R)
    {x y : (coyoneda.obj (op R)).Elements} (g : x ⟶ y) :
    phiRestrictedObj φ x ⟶ phiRestrictedObj φ y :=
  FormalObject.Hom.of (g.val)
    (fun n ↦ φ.map (phiRestrictedStageHom g n))
    (fun n ↦ truncationHom g.val n)
    sorry sorry sorry

/-- The specialized functor `Φ_R` sending `φ : underline R |_{C_Λ} ⟶ F` to the based
morphism `underline R ⟶ hat F` given by the unit of completion followed by stagewise
application of `φ`. -/
def phiRestricted (R : CompleteLocalAlgCat Λ k) :
    RestrictedHom p R ⥤
      (BasedCategory.ofFunctor (CategoryOfElements.π (coyoneda.obj (op R))) ⥤ᵇ
        BasedCategory.ofFunctor (completion p)) where
  obj φ :=
    { toFunctor :=
        { obj x := phiRestrictedObj φ x
          map g := phiRestrictedHom φ g
          map_id := sorry
          map_comp := sorry }
      w := sorry }
  map t :=
    { toNatTrans :=
        { app x :=
            FormalObject.Hom.of (𝟙 x.1)
              (fun n ↦ t.toNatTrans.app (phiRestrictedStage x n))
              (fun n ↦ 𝟙 (x.1.truncation n))
              sorry sorry sorry
          naturality := sorry }
      isHomLift' := sorry }
  map_id := sorry
  map_comp := sorry

/-- Cofibered 2-Yoneda evaluation of a based morphism `underline R ⟶ hat F` at `𝟙 R`. -/
def evaluationAtId (R : CompleteLocalAlgCat Λ k) :
    (BasedCategory.ofFunctor (CategoryOfElements.π (coyoneda.obj (op R))) ⥤ᵇ
      BasedCategory.ofFunctor (completion p)) ⥤
      Fiber (completion p) R where
  obj ψ := ⟨ψ.obj ⟨R, 𝟙 R⟩, congr_obj ψ.w ⟨R, 𝟙 R⟩⟩
  map t := ⟨t.toNatTrans.app ⟨R, 𝟙 R⟩, t.isHomLift' ⟨R, 𝟙 R⟩⟩
  map_id := sorry
  map_comp := sorry

/-- Comparison of identity-truncation presentations used by `fromRestrictedHom` and `Φ`. -/
private def fromRestrictedHom_phi_app {R : CompleteLocalAlgCat Λ k} (φ : RestrictedHom p R)
    (n : ℕ) :
    φ.obj (restrictedIdentity R n) ⟶ φ.obj (phiRestrictedStage ⟨R, 𝟙 R⟩ n) :=
  φ.map
    (CategoryOfElements.homMk (restrictedIdentity R n) (phiRestrictedStage ⟨R, 𝟙 R⟩ n)
      (𝟙 (R.truncation n)) sorry)

/-- Inverse stage comparison of identity-truncation presentations. -/
private def fromRestrictedHom_phi_app_inv {R : CompleteLocalAlgCat Λ k} (φ : RestrictedHom p R)
    (n : ℕ) :
    φ.obj (phiRestrictedStage ⟨R, 𝟙 R⟩ n) ⟶ φ.obj (restrictedIdentity R n) :=
  φ.map
    (CategoryOfElements.homMk (phiRestrictedStage ⟨R, 𝟙 R⟩ n) (restrictedIdentity R n)
      (𝟙 (R.truncation n)) sorry)

/-- `fromRestrictedHom` is the composite of `Φ_R` with cofibered 2-Yoneda evaluation at
`𝟙 R`. -/
def fromRestrictedHom_comp_phi (R : CompleteLocalAlgCat Λ k) :
    fromRestrictedHom p R ≅ phiRestricted R ⋙ evaluationAtId R where
  hom :=
    { app φ :=
        ⟨FormalObject.Hom.of (𝟙 R)
           (fun n ↦ fromRestrictedHom_phi_app φ n)
           (fun n ↦ 𝟙 (R.truncation n))
           sorry sorry sorry,
          sorry⟩
      naturality := sorry }
  inv :=
    { app φ :=
        ⟨FormalObject.Hom.of (𝟙 R)
           (fun n ↦ fromRestrictedHom_phi_app_inv φ n)
           (fun n ↦ 𝟙 (R.truncation n))
           sorry sorry sorry,
          sorry⟩
      naturality := sorry }
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Chosen pushforward of a completion fibre along a complete local map, via the
cleavage of `completion p`. -/
def iotaPush {R : CompleteLocalAlgCat Λ k}
    (ξ : Fiber (completion p) R) {S : CompleteLocalAlgCat Λ k} (f : R ⟶ S) :
    StronglyCocartesianLift (completion p) (eqToHom ξ.2 ≫ f) :=
  StronglyCocartesianLift.ofCleavage (cleavageOp (completion p)) (eqToHom ξ.2 ≫ f)

/-- The based functor `ι ξ : underline R ⟶ hat F` sending `f` to the chosen pushforward
`f_* ξ`. -/
private def iotaObj {R : CompleteLocalAlgCat Λ k} (ξ : Fiber (completion p) R) :
    BasedCategory.ofFunctor (CategoryOfElements.π (coyoneda.obj (op R))) ⥤ᵇ
      BasedCategory.ofFunctor (completion p) where
  toFunctor :=
    { obj x := (iotaPush ξ x.2).target
      map {x y} g :=
        @IsStronglyCocartesian.map _ _ _ _ (completion p) _ _ _ _
          (eqToHom ξ.2 ≫ x.2) (iotaPush ξ x.2).hom (iotaPush ξ x.2).isStronglyCocartesian
          y.1 (iotaPush ξ y.2).target g.val (eqToHom ξ.2 ≫ y.2) sorry
          (iotaPush ξ y.2).hom sorry
      map_id := sorry
      map_comp := sorry }
  w := sorry

/-- A fibre morphism over `R` induces a based 2-morphism of the corresponding `ι`
values. -/
private def iotaMap₂ {R : CompleteLocalAlgCat Λ k} {ξ η : Fiber (completion p) R} (τ : ξ ⟶ η) :
    iotaObj ξ ⟶ iotaObj η where
  toNatTrans :=
    { app x :=
        @IsStronglyCocartesian.map _ _ _ _ (completion p) _ _ _ _
          (eqToHom ξ.2 ≫ x.2) (iotaPush ξ x.2).hom (iotaPush ξ x.2).isStronglyCocartesian
          x.1 (iotaPush η x.2).target (𝟙 x.1) (eqToHom ξ.2 ≫ x.2) sorry
          (τ.1 ≫ (iotaPush η x.2).hom) sorry
      naturality := sorry }
  isHomLift' := sorry

/-- Cofibered 2-Yoneda inverse sending a formal object `ξ` over `R` to the based
morphism `f ↦ f_* ξ`. -/
def iota (R : CompleteLocalAlgCat Λ k) :
    Fiber (completion p) R ⥤
      (BasedCategory.ofFunctor (CategoryOfElements.π (coyoneda.obj (op R))) ⥤ᵇ
        BasedCategory.ofFunctor (completion p)) where
  obj ξ := iotaObj ξ
  map τ := iotaMap₂ τ
  map_id := sorry
  map_comp := sorry

/-- The value of `ι ξ` at `f : R ⟶ S` is the chosen pushforward of `ξ` along `f`. -/
theorem iota_obj_app {R S : CompleteLocalAlgCat Λ k} (ξ : Fiber (completion p) R)
    (f : R ⟶ S) :
    ((iota R).obj ξ).obj ⟨S, f⟩ = (iotaPush ξ f).target := sorry

/-- Evaluation of `ι ξ` at `𝟙 R` recovers `ξ` up to isomorphism. -/
def iota_id {R : CompleteLocalAlgCat Λ k} (ξ : Fiber (completion p) R) :
    ((iota R).obj ξ).obj ⟨R, 𝟙 R⟩ ≅ ξ.1 where
  hom :=
    @IsStronglyCocartesian.map _ _ _ _ (completion p) _ _ _ _
      (eqToHom ξ.2 ≫ 𝟙 R) (iotaPush ξ (𝟙 R)).hom (iotaPush ξ (𝟙 R)).isStronglyCocartesian
      ξ.1.base ξ.1 (eqToHom ξ.2.symm) (𝟙 ξ.1.base) sorry (𝟙 ξ.1) sorry
  inv := (iotaPush ξ (𝟙 R)).hom
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Restriction of a based morphism `underline R ⟶ hat F` along `C_Λ`, followed by the
counit `can`. -/
def psiRestricted (R : CompleteLocalAlgCat Λ k) :
    (BasedCategory.ofFunctor (CategoryOfElements.π (coyoneda.obj (op R))) ⥤ᵇ
      BasedCategory.ofFunctor (completion p)) ⥤
      RestrictedHom p R where
  obj ψ :=
    { toFunctor :=
        { obj x :=
            (can p).obj
              (Restrict.of x.1 ⟨ψ.obj ⟨inclusion.obj x.1, x.2⟩, congr_obj ψ.w ⟨inclusion.obj x.1, x.2⟩⟩)
          map {x y} f :=
            (can p).map
              { formal := ψ.map
                  (CategoryOfElements.homMk
                    (⟨inclusion.obj x.1, x.2⟩ : (coyoneda.obj (op R)).Elements)
                    (⟨inclusion.obj y.1, y.2⟩ : (coyoneda.obj (op R)).Elements)
                    (inclusion.map f.val) sorry)
                base := f.val
                over := sorry }
          map_id := sorry
          map_comp := sorry }
      w := sorry }
  map t :=
    { toNatTrans :=
        { app x :=
            (can p).map
              (Restrict.ofHom
                ⟨t.toNatTrans.app ⟨inclusion.obj x.1, x.2⟩, t.isHomLift' ⟨inclusion.obj x.1, x.2⟩⟩)
          naturality := sorry }
      isHomLift' := sorry }
  map_id := sorry
  map_comp := sorry

/-- Component of `Ψ(ι ξ) ⟶ underline ξ` at a test object `⟨A, α⟩`. -/
private def homEquivInverse_iota_app {R : CompleteLocalAlgCat Λ k}
    (ξ : Fiber (completion p) R) (x : (restrictedCoyoneda R).Elements) :
    ((psiRestricted R).obj ((iota R).obj ξ)).obj x ⟶
      ((toRestrictedHom R).obj ξ).obj x :=
  let m := nilpotencyIndex x.1
  let l := iotaPush ξ x.2
  let ψ :=
    l.hom.app m ≫
      canPush (Restrict.of x.1 ⟨l.target, congr_obj (iotaObj ξ).w ⟨inclusion.obj x.1, x.2⟩⟩)
  Along.cartesianUnop (p := p) (p.op.map (Quiver.Hom.op ψ)) (Quiver.Hom.op ψ)
    (Quiver.Hom.op (toRestrictedHomPush ξ x)) sorry sorry

/-- Inverse component of `underline ξ ⟶ Ψ(ι ξ)` at a test object. -/
private def homEquivInverse_iota_app_inv {R : CompleteLocalAlgCat Λ k}
    (ξ : Fiber (completion p) R) (x : (restrictedCoyoneda R).Elements) :
    ((toRestrictedHom R).obj ξ).obj x ⟶
      ((psiRestricted R).obj ((iota R).obj ξ)).obj x :=
  let m := nilpotencyIndex x.1
  let l := iotaPush ξ x.2
  let ψ :=
    l.hom.app m ≫
      canPush (Restrict.of x.1 ⟨l.target, congr_obj (iotaObj ξ).w ⟨inclusion.obj x.1, x.2⟩⟩)
  Along.cartesianUnop (p := p)
    (p.op.map (Quiver.Hom.op (toRestrictedHomPush ξ x))) (Quiver.Hom.op (toRestrictedHomPush ξ x))
    (Quiver.Hom.op ψ) sorry sorry

/-- `Ψ(ι ξ) ≅ underline ξ` as based morphisms over `C_Λ`. -/
def homEquivInverse_iota_iso {R : CompleteLocalAlgCat Λ k}
    (ξ : Fiber (completion p) R) :
    (psiRestricted R).obj ((iota R).obj ξ) ≅ (toRestrictedHom R).obj ξ where
  hom :=
    { toNatTrans :=
        { app x := homEquivInverse_iota_app ξ x
          naturality := sorry }
      isHomLift' := sorry }
  inv :=
    { toNatTrans :=
        { app x := homEquivInverse_iota_app_inv ξ x
          naturality := sorry }
      isHomLift' := sorry }
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Stage of `hat(underline ξ)` at a truncation of `f : R ⟶ S`. -/
private def iotaCompletionStage {R : CompleteLocalAlgCat Λ k} (ξ : Fiber (completion p) R)
    (x : (coyoneda.obj (op R)).Elements) (n : ℕ) :
    ξ.1.system.family n ⟶ ((toRestrictedHom R).obj ξ).obj (phiRestrictedStage x n) :=
  let m := nilpotencyIndex (x.1.truncation n)
  have h : m ≤ n := by sorry
  ξ.1.system.transitionMap h ≫ toRestrictedHomPush ξ (phiRestrictedStage x n)

/-- Formal morphism from `ξ` to the value of `hat(underline ξ)` at `f : R ⟶ S`. -/
private def iotaCompletionHom {R : CompleteLocalAlgCat Λ k} (ξ : Fiber (completion p) R)
    (x : (coyoneda.obj (op R)).Elements) :
    ξ.1 ⟶ ((phiRestricted R).obj ((toRestrictedHom R).obj ξ)).obj x :=
  FormalObject.Hom.of (eqToHom ξ.2 ≫ x.2)
    (fun k ↦ iotaCompletionStage ξ x k)
    (fun k ↦ truncationHom (eqToHom ξ.2 ≫ x.2) k)
    sorry sorry sorry

/-- Component of `ι ξ ⟶ hat(underline ξ)` at `f : R ⟶ S`. -/
private def iota_iso_completion_hom {R : CompleteLocalAlgCat Λ k} (ξ : Fiber (completion p) R)
    (x : (coyoneda.obj (op R)).Elements) :
    ((iota R).obj ξ).obj x ⟶ ((phiRestricted R).obj ((toRestrictedHom R).obj ξ)).obj x :=
  @IsStronglyCocartesian.map _ _ _ _ (completion p) _ _ _ _
    (eqToHom ξ.2 ≫ x.2) (iotaPush ξ x.2).hom (iotaPush ξ x.2).isStronglyCocartesian
    x.1 (((phiRestricted R).obj ((toRestrictedHom R).obj ξ)).obj x) (𝟙 x.1)
    (eqToHom ξ.2 ≫ x.2) sorry (iotaCompletionHom ξ x) sorry

/-- `ι ξ` is isomorphic to the completion of `underline ξ`. -/
def iota_iso_completion {R : CompleteLocalAlgCat Λ k} (ξ : Fiber (completion p) R) :
    (iota R).obj ξ ≅ (phiRestricted R).obj ((toRestrictedHom R).obj ξ) where
  hom :=
    { toNatTrans :=
        { app x := iota_iso_completion_hom ξ x
          naturality := sorry }
      isHomLift' := sorry }
  inv :=
    { toNatTrans :=
        { app x :=
            @IsStronglyCocartesian.map _ _ _ _ (completion p) _ _ _ _
              (eqToHom ξ.2 ≫ x.2) (iotaCompletionHom ξ x) sorry
              x.1 (iotaPush ξ x.2).target (𝟙 x.1) (eqToHom ξ.2 ≫ x.2) sorry
              (iotaPush ξ x.2).hom sorry
          naturality := sorry }
      isHomLift' := sorry }
  hom_inv_id := sorry
  inv_hom_id := sorry

end

end FormalObject

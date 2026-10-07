module

public import Mathlib.AlgebraicTopology.SimplexCategory.Defs
public import Mathlib.CategoryTheory.Category.Cat.Op
public import Mathlib.CategoryTheory.Functor.Const
public import Mathlib.CategoryTheory.Grothendieck
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import stacks_project.Chap07.Definition_7_6_2_Site

/-!
# Total site of a simplicial object in sites

Given a covariant functor `C : SimplexCategory ⥤ Cat` of continuous functors
`u_φ : C.obj m ⥤ C.obj n`, the total category is the opposite of the Grothendieck
construction of `C ⋙ Cat.opFunctor`. Chosen coverings are the identity-simplex
images of chosen stage covering families.
-/

@[expose] public section

universe u v

open CategoryTheory Opposite

namespace CategoryTheory.SimplicialSites

/-- The total category of a simplicial diagram of categories: objects are objects of some
stage `C.obj n`, and a morphism `U ⟶ V` is a simplex operator `φ : degree V ⟶ degree U`
together with a stage morphism `obj U ⟶ u_φ (obj V)`. -/
abbrev totalSite (C : SimplexCategory ⥤ Cat.{v, u}) : Type u :=
  (Grothendieck (C ⋙ Cat.opFunctor.{v, u}))ᵒᵖ

/-- The total category is the opposite of the Grothendieck construction of `C ⋙ Cat.opFunctor`. -/
theorem totalSite_def (C : SimplexCategory ⥤ Cat.{v, u}) :
    totalSite C = (Grothendieck (C ⋙ Cat.opFunctor.{v, u}))ᵒᵖ :=
  sorry

/-- The object of the total category associated to an object of the stage `C.obj n`. -/
def ofObj (C : SimplexCategory ⥤ Cat.{v, u}) (n : SimplexCategory) (U : C.obj n) :
    totalSite C :=
  op ⟨n, op U⟩

/-- The simplicial degree of an object of the total category. -/
def degree {C : SimplexCategory ⥤ Cat.{v, u}} (U : totalSite C) : SimplexCategory :=
  U.unop.base

/-- The underlying stage object of an object of the total category. -/
def obj {C : SimplexCategory ⥤ Cat.{v, u}} (U : totalSite C) : C.obj (degree U) :=
  U.unop.fiber.unop

/-- The degree of `ofObj C n U` is `n`. -/
theorem ofObj_degree (C : SimplexCategory ⥤ Cat.{v, u}) (n : SimplexCategory) (U : C.obj n) :
    degree (ofObj C n U) = n :=
  sorry

/-- The stage object of `ofObj C n U` is `U`. -/
theorem ofObj_obj (C : SimplexCategory ⥤ Cat.{v, u}) (n : SimplexCategory) (U : C.obj n) :
    obj (ofObj C n U) = U :=
  sorry

/-- Every object of the total category is `ofObj` of its degree and stage object. -/
theorem eq_ofObj {C : SimplexCategory ⥤ Cat.{v, u}} (U : totalSite C) :
    U = ofObj C (degree U) (obj U) :=
  sorry

/-- A morphism `U ⟶ V` in the total category from a simplex operator
`φ : degree V ⟶ degree U` and a stage morphism `f : obj U ⟶ u_φ (obj V)`. -/
def homMk {C : SimplexCategory ⥤ Cat.{v, u}} {U V : totalSite C}
    (φ : degree V ⟶ degree U) (f : obj U ⟶ (C.map φ).toFunctor.obj (obj V)) : U ⟶ V :=
  op ({ base := φ, fiber := op f } : V.unop ⟶ U.unop)

/-- Applying a composite simplex operator is the composite of the corresponding stage functors. -/
theorem map_comp_toFunctor_obj (C : SimplexCategory ⥤ Cat.{v, u})
    {k m n : SimplexCategory} (ψ : k ⟶ m) (φ : m ⟶ n) (W : C.obj k) :
    (C.map φ).toFunctor.obj ((C.map ψ).toFunctor.obj W) =
      (C.map (ψ ≫ φ)).toFunctor.obj W :=
  sorry

/-- Composition of total-category morphisms is `(φ, f) ≫ (ψ, g) = (ψ ≫ φ, f ≫ u_φ(g))`. -/
theorem homMk_comp {C : SimplexCategory ⥤ Cat.{v, u}} {U V W : totalSite C}
    (φ : degree V ⟶ degree U) (f : obj U ⟶ (C.map φ).toFunctor.obj (obj V))
    (ψ : degree W ⟶ degree V) (g : obj V ⟶ (C.map ψ).toFunctor.obj (obj W)) :
    homMk φ f ≫ homMk ψ g =
      homMk (ψ ≫ φ)
        (f ≫ (C.map φ).toFunctor.map g ≫ eqToHom (map_comp_toFunctor_obj C ψ φ (obj W))) :=
  sorry

/-- Unpack a total-category morphism as the source pair `(φ, f)`. -/
def homToPair {C : SimplexCategory ⥤ Cat.{v, u}} {U V : totalSite C} (f : U ⟶ V) :
    Σ φ : degree V ⟶ degree U, obj U ⟶ (C.map φ).toFunctor.obj (obj V) :=
  ⟨f.unop.base, f.unop.fiber.unop⟩

/-- Morphisms `U ⟶ V` in the total category are pairs `(φ, f)` with
`φ : degree V ⟶ degree U` and `f : obj U ⟶ u_φ (obj V)`. -/
def homEquiv {C : SimplexCategory ⥤ Cat.{v, u}} {U V : totalSite C} :
    (U ⟶ V) ≃ Σ φ : degree V ⟶ degree U, obj U ⟶ (C.map φ).toFunctor.obj (obj V) where
  toFun := homToPair
  invFun p := homMk p.1 p.2
  left_inv := sorry
  right_inv := sorry

/-- `homEquiv` unpacks a total-category morphism as its simplex operator and stage morphism. -/
theorem homEquiv_apply {C : SimplexCategory ⥤ Cat.{v, u}} {U V : totalSite C} (f : U ⟶ V) :
    homEquiv f = homToPair f :=
  sorry

/-- The inverse of `homEquiv` is `homMk`. -/
theorem homEquiv_symm_apply {C : SimplexCategory ⥤ Cat.{v, u}} {U V : totalSite C}
    (φ : degree V ⟶ degree U) (f : obj U ⟶ (C.map φ).toFunctor.obj (obj V)) :
    homEquiv.symm ⟨φ, f⟩ = homMk φ f :=
  sorry

/-- The inclusion of the stage `C.obj n` into the total category on the identity simplex. -/
def ofStage (C : SimplexCategory ⥤ Cat.{v, u}) (n : SimplexCategory) :
    C.obj n ⥤ totalSite C where
  obj U := ofObj C n U
  map {X Y} f :=
    homMk (𝟙 n)
      (f ≫ eqToHom ((congrArg (fun G : C.obj n ⟶ C.obj n ↦ G.toFunctor.obj Y)
        (C.map_id n)).trans (Cat.Hom.id_obj Y)).symm)
  map_id := sorry
  map_comp := sorry

/-- `ofStage C n` sends a stage object `U` to `ofObj C n U`. -/
theorem ofStage_obj (C : SimplexCategory ⥤ Cat.{v, u}) (n : SimplexCategory) (U : C.obj n) :
    (ofStage C n).obj U = ofObj C n U :=
  sorry

/-- The identity-simplex family in the total category associated to a family of stage morphisms. -/
def ofStageArrows {C : SimplexCategory ⥤ Cat.{v, u}} {U : totalSite C}
    {ι : Type (max u v)} (X : ι → C.obj (degree U)) (f : ∀ i, X i ⟶ obj U) : Presieve U :=
  Presieve.ofArrows (fun i ↦ (ofStage C (degree U)).obj (X i))
    (fun i ↦ (ofStage C (degree U)).map (f i))

/-- `ofStageArrows` is the `ofArrows` family of identity-simplex images of the stage morphisms. -/
theorem ofStageArrows_eq {C : SimplexCategory ⥤ Cat.{v, u}} {U : totalSite C}
    {ι : Type (max u v)} (X : ι → C.obj (degree U)) (f : ∀ i, X i ⟶ obj U) :
    ofStageArrows X f =
      Presieve.ofArrows (fun i ↦ (ofStage C (degree U)).obj (X i))
        (fun i ↦ (ofStage C (degree U)).map (f i)) :=
  sorry

/-- A `Cat`-valued simplex diagram whose stages are sites and whose structure maps are
continuous for the chosen stage precoverages. -/
class IsSiteDiagram (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n)) : Prop where
  /-- Each stage precoverage is a site. -/
  isSite : ∀ n, (J n).IsSite
  /-- Each structure map `u_φ : C.obj m ⥤ C.obj n` preserves chosen covers and covering-arrow
  pullbacks. -/
  isContinuous : ∀ {m n : SimplexCategory} (φ : m ⟶ n),
    Functor.Precoverage.IsContinuous (C.map φ).toFunctor (J m) (J n)

/-- A simplicial site diagram is exactly stagewise `IsSite` together with selected-cover
continuity of every structure map. -/
theorem IsSiteDiagram.iff (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n)) :
    IsSiteDiagram C J ↔
      (∀ n, (J n).IsSite) ∧
        ∀ {m n : SimplexCategory} (φ : m ⟶ n),
          Functor.Precoverage.IsContinuous (C.map φ).toFunctor (J m) (J n) :=
  sorry

/-- A constant diagram of a site is a simplicial site diagram. -/
instance IsSiteDiagram.const {C : Type u} [Category.{v} C] (J : Precoverage C) [J.IsSite] :
    IsSiteDiagram ((Functor.const SimplexCategory).obj (Cat.of C)) (fun _ ↦ J) :=
  sorry

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))

/-- Covering families in the total category are identity-simplex images of chosen stage covering
families. -/
def precoverage : Precoverage (totalSite C) where
  coverings U :=
    {R | ∃ (ι : Type (max u v)) (X : ι → C.obj (degree U)) (f : ∀ i, X i ⟶ obj U),
      R = ofStageArrows X f ∧ Presieve.ofArrows X f ∈ J (degree U) (obj U)}

/-- A presieve covers in the total precoverage iff it is the identity-simplex image of a chosen
stage covering family. -/
theorem mem_precoverage_iff {U : totalSite C} {R : Presieve U} :
    R ∈ precoverage C J U ↔
      ∃ (ι : Type (max u v)) (X : ι → C.obj (degree U)) (f : ∀ i, X i ⟶ obj U),
        R = ofStageArrows X f ∧ Presieve.ofArrows X f ∈ J (degree U) (obj U) :=
  sorry

/-- An identity-simplex family covers in `precoverage C J` iff the underlying stage family
covers. -/
theorem ofStageArrows_mem_iff {U : totalSite C} {ι : Type (max u v)}
    (X : ι → C.obj (degree U)) (f : ∀ i, X i ⟶ obj U) :
    ofStageArrows X f ∈ precoverage C J U ↔
      Presieve.ofArrows X f ∈ J (degree U) (obj U) :=
  sorry

/-- In the simplicial case, `SimplexCategory.eq_id_of_isIso` makes every total-category
isomorphism identity-degree, so it reduces to a stage isomorphism and singleton isomorphisms
cover. -/
instance precoverage.hasIsos [IsSiteDiagram C J] : (precoverage C J).HasIsos :=
  sorry

/-- Identity-simplex stage coverings are stable under bind. -/
instance precoverage.isStableUnderBind [IsSiteDiagram C J] :
    (precoverage C J).IsStableUnderBind :=
  sorry

/-- Covering arrows in the identity-simplex stage precoverage admit pullbacks. -/
instance precoverage.hasPullbacks [IsSiteDiagram C J] : (precoverage C J).HasPullbacks :=
  sorry

/-- After base change, an identity-simplex covering is refined by a covering that factors through
the original family. -/
instance precoverage.hasFactoringPullbacks [IsSiteDiagram C J] :
    (precoverage C J).HasFactoringPullbacks :=
  sorry

/-- Pulling back an identity-simplex covering `{f i}` along `g : W ⟶ U` yields the
identity-simplex family of stage fibre products `W ×_{u_φ(U)} u_φ(U_i)` in `C.obj (degree W)`.
Each square with legs `(ofStage C (degree W)).map (p i)`, the comparison
`homMk g.unop.base (q i)`, `g`, and `(ofStage C (degree U)).map (f i)` is a pullback in
the total category; this is `W ×_{(φ, g)} U_i = W ×_{g, u_φ(U), u_φ(f i)} u_φ(U_i)`,
not `Presieve.pullbackArrows`. -/
theorem exists_ofStage_isPullback [IsSiteDiagram C J] {U W : totalSite C} (g : W ⟶ U)
    {ι : Type (max u v)} (X : ι → C.obj (degree U)) (f : ∀ i, X i ⟶ obj U)
    (hf : Presieve.ofArrows X f ∈ J (degree U) (obj U)) :
    ∃ (P : ι → C.obj (degree W)) (p : ∀ i, P i ⟶ obj W)
      (q : ∀ i, P i ⟶ (C.map g.unop.base).toFunctor.obj (X i)),
      ofStageArrows P p ∈ precoverage C J W ∧
        ∀ i, IsPullback ((ofStage C (degree W)).map (p i))
          (homMk g.unop.base (q i) :
            (ofStage C (degree W)).obj (P i) ⟶ (ofStage C (degree U)).obj (X i))
          g ((ofStage C (degree U)).map (f i)) :=
  sorry

/-- The Grothendieck topology generated by the identity-simplex stage precoverage. -/
def topology : GrothendieckTopology (totalSite C) :=
  (precoverage C J).toGrothendieck

/-- The total-site topology is generated by `precoverage C J`. -/
theorem topology_eq_toGrothendieck : topology C J = (precoverage C J).toGrothendieck :=
  sorry

end CategoryTheory.SimplicialSites

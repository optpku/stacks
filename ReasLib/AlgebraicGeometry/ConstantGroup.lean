/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.Topology.LocallyConstant.Algebra
public import ReasLib.AlgebraicGeometry.Scheme.Coproduct

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry CategoryTheory.MonObj MonoidalCategory

universe u

namespace AlgebraicGeometry.ConstantGroup

/-- The constant scheme attached to `G` is the coproduct of copies of `Spec ℤ`
indexed by the elements of `G`. -/
noncomputable def scheme (G : GrpCat.{u}) : Scheme.{u} :=
  ∐ fun _ : G ↦ Spec (.of (ULift.{u} ℤ))

/-- The carrier of `scheme G` is its defining coproduct. -/
theorem scheme_def (G : GrpCat.{u}) :
    scheme G = ∐ fun _ : G ↦ Spec (.of (ULift.{u} ℤ)) := sorry

/-- The constant scheme over `Spec ℤ`, with the fold map as structure morphism. -/
noncomputable def schemeOverSpecZ (G : GrpCat.{u}) :
    Over (Spec (.of (ULift.{u} ℤ))) :=
  Over.mk (Sigma.desc fun _ : G ↦ 𝟙 (Spec (.of (ULift.{u} ℤ))))

/-- The underlying scheme of `schemeOverSpecZ G` is `scheme G`. -/
theorem schemeOverSpecZ_left (G : GrpCat.{u}) :
    (schemeOverSpecZ G).left = scheme G := sorry

/-- The structure morphism of `schemeOverSpecZ G` is the coproduct fold map. -/
theorem schemeOverSpecZ_hom (G : GrpCat.{u}) :
    (schemeOverSpecZ G).hom =
      Sigma.desc (fun _ : G ↦ 𝟙 (Spec (.of (ULift.{u} ℤ)))) := sorry

/-- Precomposition of locally constant functions along a morphism over `S`. -/
def pointsMap {S : Scheme.{u}} (G : GrpCat.{u}) {T T' : Over S} (f : T ⟶ T') :
    GrpCat.of (LocallyConstant T'.left G) ⟶ GrpCat.of (LocallyConstant T.left G) :=
  GrpCat.ofHom (LocallyConstant.comapMonoidHom f.left.base.hom)

/-- The map on constant-group points is precomposition on values. -/
theorem pointsMap_apply {S : Scheme.{u}} (G : GrpCat.{u}) {T T' : Over S}
    (f : T ⟶ T') (a : LocallyConstant T'.left G) (x : T.left) :
    pointsMap G f a x = a (f.left x) := sorry

/-- Identity morphisms induce identity maps on locally constant points. -/
theorem pointsMap_id {S : Scheme.{u}} (G : GrpCat.{u}) (T : Over S) :
    pointsMap G (𝟙 T) = 𝟙 (GrpCat.of (LocallyConstant T.left G)) := sorry

/-- Composition of scheme morphisms induces contravariant composition on points. -/
theorem pointsMap_comp {S : Scheme.{u}} (G : GrpCat.{u})
    {T₁ T₂ T₃ : Over S} (f : T₁ ⟶ T₂) (g : T₂ ⟶ T₃) :
    pointsMap G (f ≫ g) = pointsMap G g ≫ pointsMap G f := sorry

/-- The group-valued functor of locally constant `G`-valued maps on `S`-schemes. -/
def points (S : Scheme.{u}) (G : GrpCat.{u}) : (Over S)ᵒᵖ ⥤ GrpCat.{u} where
  obj T := GrpCat.of (LocallyConstant T.unop.left G)
  map f := pointsMap G f.unop
  map_id T := pointsMap_id G T.unop
  map_comp f g := pointsMap_comp G g.unop f.unop

/-- Objects of `points S G` are locally constant maps into `G`. -/
theorem points_obj (S : Scheme.{u}) (G : GrpCat.{u}) (T : (Over S)ᵒᵖ) :
    (points S G).obj T = GrpCat.of (LocallyConstant T.unop.left G) := sorry

/-- The action of `points S G` on a morphism is the corresponding precomposition map. -/
theorem points_map (S : Scheme.{u}) (G : GrpCat.{u}) {T T' : (Over S)ᵒᵖ}
    (f : T ⟶ T') : (points S G).map f = pointsMap G f.unop := sorry

/-- The inverse image of one value of a locally constant function, as an open subscheme. -/
def fiber {S : Scheme.{u}} (G : GrpCat.{u}) (T : Over S)
    (a : LocallyConstant T.left G) (g : G) : T.left.Opens :=
  ⟨a ⁻¹' {g}, a.isLocallyConstant {g}⟩

/-- Membership in a fibre is equality with its indexing value. -/
private theorem mem_fiber_iff {S : Scheme.{u}} (G : GrpCat.{u}) (T : Over S)
    (a : LocallyConstant T.left G) (g : G) (x : T.left) :
    x ∈ fiber G T a g ↔ a x = g := sorry

/-- The fibres of a locally constant function form an open cover. -/
theorem fiber_isOpenCover {S : Scheme.{u}} (G : GrpCat.{u}) (T : Over S)
    (a : LocallyConstant T.left G) :
    TopologicalSpace.IsOpenCover (fiber G T a) := sorry

/-- The open cover of a scheme by the fibres of a locally constant function. -/
def fiberCover {S : Scheme.{u}} (G : GrpCat.{u}) (T : Over S)
    (a : LocallyConstant T.left G) : T.left.OpenCover :=
  T.left.openCoverOfIsOpenCover (fiber G T a) (fiber_isOpenCover G T a)

/-- The objects in the fibre cover are the corresponding open subschemes. -/
private theorem fiberCover_X {S : Scheme.{u}} (G : GrpCat.{u}) (T : Over S)
    (a : LocallyConstant T.left G) (g : G) :
    (fiberCover G T a).X g = (fiber G T a g).toScheme := sorry

/-- The morphism from one fibre into its indexed coproduct component. -/
def fiberMorphism {S : Scheme.{u}} (G : GrpCat.{u}) (T : Over S)
    (a : LocallyConstant T.left G) (g : G) : (fiberCover G T a).X g ⟶ scheme G :=
  specULiftZIsTerminal.from ((fiberCover G T a).X g) ≫
    Sigma.ι (fun _ : G ↦ Spec (.of (ULift.{u} ℤ))) g

/-- The local fibre morphism factors through the component indexed by that fibre. -/
private theorem fiberMorphism_def {S : Scheme.{u}} (G : GrpCat.{u}) (T : Over S)
    (a : LocallyConstant T.left G) (g : G) :
    fiberMorphism G T a g = specULiftZIsTerminal.from ((fiberCover G T a).X g) ≫
      Sigma.ι (fun _ : G ↦ Spec (.of (ULift.{u} ℤ))) g := sorry

/-- Local morphisms from fibres agree over their pairwise intersections. -/
theorem fiberMorphism_compatible {S : Scheme.{u}} (G : GrpCat.{u}) (T : Over S)
    (a : LocallyConstant T.left G) (g h : G) :
    pullback.fst ((fiberCover G T a).f g) ((fiberCover G T a).f h) ≫
        fiberMorphism G T a g =
      pullback.snd ((fiberCover G T a).f g) ((fiberCover G T a).f h) ≫
        fiberMorphism G T a h := sorry

/-- Gluing the fibre morphisms gives the morphism classified by a locally constant map. -/
def gluedMorphism {S : Scheme.{u}} (G : GrpCat.{u}) (T : Over S)
    (a : LocallyConstant T.left G) : T.left ⟶ scheme G :=
  (fiberCover G T a).glueMorphisms (fiberMorphism G T a)
    (fiberMorphism_compatible G T a)

/-- The glued morphism restricts to the prescribed morphism on each fibre. -/
private theorem gluedMorphism_fiber {S : Scheme.{u}} (G : GrpCat.{u}) (T : Over S)
    (a : LocallyConstant T.left G) (g : G) :
    (fiberCover G T a).f g ≫ gluedMorphism G T a = fiberMorphism G T a g := sorry

/-- The glued morphism commutes with the structure maps to `Spec ℤ`. -/
theorem gluedMorphism_over (G : GrpCat.{u})
    (T : Over (Spec (.of (ULift.{u} ℤ))))
    (a : LocallyConstant T.left G) :
    gluedMorphism G T a ≫ (schemeOverSpecZ G).hom = T.hom := sorry

/-- The morphism over `Spec ℤ` classified by a locally constant map. -/
def morphismOfPoint (G : GrpCat.{u})
    (T : Over (Spec (.of (ULift.{u} ℤ))))
    (a : LocallyConstant T.left G) : T ⟶ schemeOverSpecZ G :=
  Over.homMk (gluedMorphism G T a) (gluedMorphism_over G T a)

/-- The underlying scheme map classified by a locally constant function is its glued map. -/
private theorem morphismOfPoint_left (G : GrpCat.{u})
    (T : Over (Spec (.of (ULift.{u} ℤ))))
    (a : LocallyConstant T.left G) :
    (morphismOfPoint G T a).left = gluedMorphism G T a := sorry

/-- A morphism to the coproduct determines its locally constant component index. -/
theorem pointOfMorphism_isLocallyConstant (G : GrpCat.{u})
    (T : Over (Spec (.of (ULift.{u} ℤ)))) (f : T ⟶ schemeOverSpecZ G) :
    IsLocallyConstant (fun x ↦
      ((AlgebraicGeometry.sigmaMk
        (fun _ : G ↦ Spec (.of (ULift.{u} ℤ)))).symm (f.left x)).1) := sorry

/-- The locally constant component-index map associated to a morphism to the coproduct. -/
def pointOfMorphism (G : GrpCat.{u})
    (T : Over (Spec (.of (ULift.{u} ℤ))))
    (f : T ⟶ schemeOverSpecZ G) : LocallyConstant T.left G :=
  ⟨fun x ↦ ((AlgebraicGeometry.sigmaMk
    (fun _ : G ↦ Spec (.of (ULift.{u} ℤ)))).symm
    (f.left x)).1, pointOfMorphism_isLocallyConstant G T f⟩

/-- The component-index function evaluates by applying the coproduct homeomorphism. -/
private theorem pointOfMorphism_apply (G : GrpCat.{u})
    (T : Over (Spec (.of (ULift.{u} ℤ))))
    (f : T ⟶ schemeOverSpecZ G) (x : T.left) :
    pointOfMorphism G T f x =
      ((AlgebraicGeometry.sigmaMk
        (fun _ : G ↦ Spec (.of (ULift.{u} ℤ)))).symm (f.left x)).1 := sorry

/-- Gluing the fibres of a component-index map recovers the original morphism. -/
theorem morphismOfPoint_pointOfMorphism (G : GrpCat.{u})
    (T : Over (Spec (.of (ULift.{u} ℤ)))) (f : T ⟶ schemeOverSpecZ G) :
    morphismOfPoint G T (pointOfMorphism G T f) = f := sorry

/-- Extracting component indices from the glued morphism recovers the original function. -/
theorem pointOfMorphism_morphismOfPoint (G : GrpCat.{u})
    (T : Over (Spec (.of (ULift.{u} ℤ)))) (a : LocallyConstant T.left G) :
    pointOfMorphism G T (morphismOfPoint G T a) = a := sorry

/-- Morphisms to the constant coproduct are equivalent to locally constant `G`-valued maps. -/
noncomputable def homEquiv (G : GrpCat.{u})
    (T : Over (Spec (.of (ULift.{u} ℤ)))) :
    (T ⟶ schemeOverSpecZ G) ≃ LocallyConstant T.left G where
  toFun := pointOfMorphism G T
  invFun := morphismOfPoint G T
  left_inv := morphismOfPoint_pointOfMorphism G T
  right_inv := pointOfMorphism_morphismOfPoint G T

/-- The forward map of `homEquiv` extracts the coproduct component index. -/
theorem homEquiv_apply (G : GrpCat.{u})
    (T : Over (Spec (.of (ULift.{u} ℤ))))
    (f : T ⟶ schemeOverSpecZ G) (x : T.left) :
    homEquiv G T f x =
      ((AlgebraicGeometry.sigmaMk
        (fun _ : G ↦ Spec (.of (ULift.{u} ℤ)))).symm (f.left x)).1 := sorry

/-- The inverse of `homEquiv` is the morphism obtained by gluing its fibre maps. -/
private theorem homEquiv_symm_left (G : GrpCat.{u})
    (T : Over (Spec (.of (ULift.{u} ℤ))))
    (a : LocallyConstant T.left G) :
    ((homEquiv G T).symm a).left = gluedMorphism G T a := sorry

/-- The equivalence with locally constant maps is natural under precomposition. -/
theorem homEquiv_comp (G : GrpCat.{u})
    {T T' : Over (Spec (.of (ULift.{u} ℤ)))} (f : T ⟶ T')
    (g : T' ⟶ schemeOverSpecZ G) :
    homEquiv G T (f ≫ g) =
      ((points (Spec (.of (ULift.{u} ℤ))) G ⋙ forget GrpCat).map f.op)
        (homEquiv G T' g) := sorry

/-- The locally constant point functor is represented by the constant coproduct scheme. -/
noncomputable def representedBy (G : GrpCat.{u}) :
    (points (Spec (.of (ULift.{u} ℤ))) G ⋙ forget GrpCat).RepresentableBy
      (schemeOverSpecZ G) where
  homEquiv := homEquiv G _
  homEquiv_comp := homEquiv_comp G

/-- The representing equivalence supplied by `representedBy` is `homEquiv`. -/
theorem representedBy_homEquiv (G : GrpCat.{u})
    (T : Over (Spec (.of (ULift.{u} ℤ)))) :
    (representedBy G).homEquiv = homEquiv G T := sorry

/-- The representing coproduct carries the canonical internal group structure. -/
noncomputable instance instGrpObjSchemeOverSpecZ (G : GrpCat.{u}) :
    GrpObj (schemeOverSpecZ G) :=
  CategoryTheory.GrpObj.ofRepresentableBy (schemeOverSpecZ G)
    (points (Spec (.of (ULift.{u} ℤ))) G) (representedBy G)

/-- The constant group scheme over `Spec ℤ`. -/
noncomputable def overSpecZ (G : GrpCat.{u}) :
    Grp (Over (Spec (.of (ULift.{u} ℤ)))) :=
  { X := schemeOverSpecZ G }

/-- The underlying object of `overSpecZ G` is the constant coproduct over `Spec ℤ`. -/
theorem overSpecZ_X (G : GrpCat.{u}) : (overSpecZ G).X = schemeOverSpecZ G := sorry

/-- The component inclusion is a morphism from the tensor unit over `Spec ℤ`. -/
theorem component_over (G : GrpCat.{u}) (g : G) :
    Sigma.ι (fun _ : G ↦ Spec (.of (ULift.{u} ℤ))) g ≫ (schemeOverSpecZ G).hom =
      (𝟙_ (Over (Spec (.of (ULift.{u} ℤ))))).hom := sorry

/-- The inclusion of the coproduct component indexed by `g`. -/
noncomputable def component (G : GrpCat.{u}) (g : G) :
    𝟙_ (Over (Spec (.of (ULift.{u} ℤ))) ) ⟶ (overSpecZ G).X :=
  Over.homMk (Sigma.ι (fun _ : G ↦ Spec (.of (ULift.{u} ℤ))) g) (component_over G g)

/-- The underlying scheme morphism of `component G g` is the coproduct inclusion. -/
theorem component_left (G : GrpCat.{u}) (g : G) :
    (component G g).left = Sigma.ι (fun _ : G ↦ Spec (.of (ULift.{u} ℤ))) g := sorry

/-- Multiplication sends the `(g, g')` component to the `g * g'` component. -/
theorem mul_component (G : GrpCat.{u}) (g g' : G) :
    CartesianMonoidalCategory.lift (component G g) (component G g') ≫
      μ[(overSpecZ G).X] = component G (g * g') := sorry

/-- The unit of the constant group scheme is its identity component. -/
theorem one_component (G : GrpCat.{u}) :
    η[(overSpecZ G).X] = component G 1 := sorry

/-- Inversion carries the `g` component to the `g⁻¹` component. -/
theorem inv_component (G : GrpCat.{u}) (g : G) :
    component G g ≫ ι[(overSpecZ G).X] = component G g⁻¹ := sorry

/-- The group-valued Yoneda functor of the constant group scheme is its point functor. -/
noncomputable def pointsIso (G : GrpCat.{u}) :
    CategoryTheory.yonedaGrp.obj (overSpecZ G) ≅
      points (Spec (.of (ULift.{u} ℤ))) G :=
  CategoryTheory.yonedaGrpObjIsoOfRepresentableBy (schemeOverSpecZ G)
    (points (Spec (.of (ULift.{u} ℤ))) G) (representedBy G)

/-- The forward component of `pointsIso` is the representing equivalence. -/
theorem pointsIso_hom_app (G : GrpCat.{u})
    (T : Over (Spec (.of (ULift.{u} ℤ)))) (f : T ⟶ (overSpecZ G).X) :
    (pointsIso G).hom.app (op T) f = homEquiv G T f := sorry

/-- The constant group scheme over `S`, obtained by base change from `Spec ℤ`. -/
noncomputable def baseChange (S : Scheme.{u}) (G : GrpCat.{u}) : Grp (Over S) :=
  (Over.pullback (specULiftZIsTerminal.from S)).mapGrp.obj (overSpecZ G)

/-- The underlying object of `baseChange S G` is the canonical pullback of the
constant coproduct over `Spec ℤ`. -/
theorem baseChange_X (S : Scheme.{u}) (G : GrpCat.{u}) :
    (baseChange S G).X =
      (Over.pullback (specULiftZIsTerminal.from S)).obj (schemeOverSpecZ G) := sorry

/-- The pullback adjunction identifies relative points with absolute points of the
constant group scheme. -/
noncomputable def baseChangeHomEquivAbsolute (S : Scheme.{u}) (G : GrpCat.{u})
    (T : Over S) :
    (T ⟶ (baseChange S G).X) ≃
      ((Over.map (specULiftZIsTerminal.from S)).obj T ⟶ (overSpecZ G).X) :=
  (Over.mapPullbackAdj (specULiftZIsTerminal.from S)).homEquiv
    T (overSpecZ G).X |>.symm

/-- The forward map of `baseChangeHomEquivAbsolute` is the pullback-adjunction
comparison on relative points. -/
theorem baseChangeHomEquivAbsolute_apply (S : Scheme.{u}) (G : GrpCat.{u})
    (T : Over S) (f : T ⟶ (baseChange S G).X) :
    baseChangeHomEquivAbsolute S G T f =
      ((Over.mapPullbackAdj (specULiftZIsTerminal.from S)).homEquiv
        T (overSpecZ G).X).symm f := sorry

/-- Relative points of the constant group scheme are locally constant `G`-valued maps. -/
noncomputable def baseChangeHomEquiv (S : Scheme.{u}) (G : GrpCat.{u})
    (T : Over S) :
    (T ⟶ (baseChange S G).X) ≃ LocallyConstant T.left G :=
  (baseChangeHomEquivAbsolute S G T).trans
    (homEquiv G ((Over.map (specULiftZIsTerminal.from S)).obj T))

/-- The relative point equivalence respects multiplication. -/
theorem baseChangeHomEquiv_map_mul (S : Scheme.{u}) (G : GrpCat.{u})
    (T : Over S) (f g : T ⟶ (baseChange S G).X) :
    baseChangeHomEquiv S G T (f * g) =
      baseChangeHomEquiv S G T f * baseChangeHomEquiv S G T g := sorry

/-- The multiplicative equivalence between relative points and locally constant maps. -/
noncomputable def baseChangeHomMulEquiv (S : Scheme.{u}) (G : GrpCat.{u})
    (T : Over S) :
    (T ⟶ (baseChange S G).X) ≃* LocallyConstant T.left G where
  toEquiv := baseChangeHomEquiv S G T
  map_mul' := baseChangeHomEquiv_map_mul S G T

/-- The multiplicative point equivalence has the same underlying function as
`baseChangeHomEquiv`. -/
theorem baseChangeHomMulEquiv_apply (S : Scheme.{u}) (G : GrpCat.{u})
    (T : Over S) (f : T ⟶ (baseChange S G).X) :
    baseChangeHomMulEquiv S G T f = baseChangeHomEquiv S G T f := sorry

/-- The objectwise group isomorphism between relative points and locally constant maps. -/
noncomputable def baseChangeComponentIso (S : Scheme.{u}) (G : GrpCat.{u})
    (T : (Over S)ᵒᵖ) :
    (CategoryTheory.yonedaGrp.obj (baseChange S G)).obj T ≅ (points S G).obj T :=
  MulEquiv.toGrpIso (baseChangeHomMulEquiv S G T.unop)

/-- Naturality of the locally constant description of relative points. -/
theorem baseChangeComponentIso_naturality (S : Scheme.{u}) (G : GrpCat.{u})
    {T T' : (Over S)ᵒᵖ} (f : T ⟶ T') :
    (CategoryTheory.yonedaGrp.obj (baseChange S G)).map f ≫
        (baseChangeComponentIso S G T').hom =
      (baseChangeComponentIso S G T).hom ≫ (points S G).map f := sorry

/-- The group-valued functor of points of `baseChange S G` is the functor of locally
constant `G`-valued maps. -/
noncomputable def baseChangePointsIso (S : Scheme.{u}) (G : GrpCat.{u}) :
    CategoryTheory.yonedaGrp.obj (baseChange S G) ≅ points S G :=
  NatIso.ofComponents (baseChangeComponentIso S G)
    (fun f ↦ baseChangeComponentIso_naturality S G f)

/-- The forward component of `baseChangePointsIso` is the relative point equivalence. -/
theorem baseChangePointsIso_hom_app (S : Scheme.{u}) (G : GrpCat.{u})
    (T : Over S) (f : T ⟶ (baseChange S G).X) :
    (baseChangePointsIso S G).hom.app (op T) f = baseChangeHomEquiv S G T f := sorry

end AlgebraicGeometry.ConstantGroup

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RationalFunction.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale
public import ReasLib.AlgebraicGeometry.Scheme.RationalFunction

/-! 
# Rational functions on a supplied étale scheme chart

The open domain of a partial map already carries relative representability data. Pulling
that domain back to a supplied scheme chart gives a scheme and an actual open immersion.
Its native open-image isomorphism turns the coordinate function into a section on a dense
open of the chart, hence into a scheme rational function.
-/

@[expose] public section
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry
noncomputable section
universe u

namespace AlgebraicGeometry.AlgebraicSpace.RationalFunctionChart

variable {S : Scheme.{u}} {X : AlgebraicSpace S}
variable (f : PartialMap X (affineLine S)) (T : Over S) (p : ofOver T ⟶ X)

/-- The scheme representing the actual pullback of the domain to the given chart. -/
def domainOver : Over S := f.domain.prop.presheaf.1.pullback p

/-- The represented pullback's actual morphism to the chart. -/
def domainInclusion : domainOver f T p ⟶ T := f.domain.prop.presheaf.1.snd p

/-- The projection from the pulled-back open domain to the chart is an open immersion. -/
def domainInclusion_isOpenImmersion :
    AlgebraicGeometry.IsOpenImmersion (domainInclusion f T p).left :=
  f.domain.prop.presheaf.property_snd p

/-- The represented pullback square supplied by the input open-domain data. -/
theorem domain_isPullback :
    IsPullback (f.domain.prop.presheaf.1.fst p) (yoneda.map (domainInclusion f T p))
      f.domain.hom p :=
  f.domain.prop.presheaf.1.isPullback p

/-- The actual map to the affine line on the represented domain, extracted by native Yoneda. -/
def domainCoordinateMap : domainOver f T p ⟶ affineLineOver S :=
  yonedaEquiv (f.domain.prop.presheaf.1.fst p ≫ f.hom)

/-- The actual coordinate section on the represented scheme domain. -/
def domainSection : Γ((domainOver f T p).left, ⊤) :=
  coordHom (domainCoordinateMap f T p)

/-- The actual image open inside the supplied scheme chart. -/
def domainOpen : T.left.Opens :=
  @Scheme.Hom.opensRange _ _ (domainInclusion f T p).left
    (domainInclusion_isOpenImmersion f T p)

/-- Transport the actual section to the image open using the native open-immersion inverse. -/
def openSection : Γ(T.left, domainOpen f T p) :=
  (domainOpen f T p).topIso.hom
    ((@Scheme.Hom.isoOpensRange _ _ (domainInclusion f T p).left
      (domainInclusion_isOpenImmersion f T p)).inv.appTop (domainSection f T p))

/-- Étale pullback preserves the density of the supplied open domain. -/
theorem domainOpen_dense [Etale p] : Dense (domainOpen f T p : Set T.left) := sorry

/-- The scheme rational function defined by the pulled-back partial map. -/
def partialValue [Etale p] : Scheme.RationalFunction T.left :=
  Scheme.RationalFunction.stage T.left ⟨domainOpen f T p, domainOpen_dense f T p⟩
    (openSection f T p)

/-- Agreement on a dense open remains agreement after the actual chart pullback. -/
theorem partialValue_eq_of_equiv [Etale p] {g : PartialMap X (affineLine S)}
    (h : PartialMap.equiv f g) : partialValue f T p = partialValue g T p := sorry

/-- The rational function on a supplied étale scheme chart induced by a rational function. -/
def value [Etale p] : RationalFunction X → Scheme.RationalFunction T.left :=
  Quotient.lift (fun f ↦ partialValue f T p)
    (fun f g h ↦ partialValue_eq_of_equiv f T p h)

/-- Pullback to an étale scheme chart preserves the zero rational function. -/
theorem value_zero [Etale p] : value T p 0 = 0 := sorry

/-- Pullback to an étale scheme chart preserves the unit rational function. -/
theorem value_one [Etale p] : value T p 1 = 1 := sorry

/-- Pullback to an étale scheme chart preserves addition of rational functions. -/
theorem value_add [Etale p] (a b : RationalFunction X) :
    value T p (a + b) = value T p a + value T p b := sorry

/-- Pullback to an étale scheme chart preserves multiplication of rational functions. -/
theorem value_mul [Etale p] (a b : RationalFunction X) :
    value T p (a * b) = value T p a * value T p b := sorry

/-- Pull rational functions back to a supplied étale scheme chart. No affine or integral
hypothesis on the chart is required. -/
def map [Etale p] : RationalFunction X →+* Scheme.RationalFunction T.left where
  toFun := value T p
  map_zero' := value_zero T p
  map_one' := value_one T p
  map_add' := value_add T p
  map_mul' := value_mul T p

/-- The chart map computes on the actual partial-map representative. -/
theorem map_toRationalMap [Etale p] : map T p f.toRationalMap = partialValue f T p := rfl

/-- A representative is sent to its actual coordinate section on the image open. -/
theorem map_toRationalMap_stage [Etale p] : map T p f.toRationalMap =
    Scheme.RationalFunction.stage T.left ⟨domainOpen f T p, domainOpen_dense f T p⟩
      (openSection f T p) := rfl

end AlgebraicGeometry.AlgebraicSpace.RationalFunctionChart

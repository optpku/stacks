module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Conormal.Etale
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Limits

universe u

/- Lemma 76.5.2: Let `S` be a scheme. Let `i : Z ⟶ X` be an immersion. Let
`φ : U ⟶ X` be an étale morphism where `U` is a scheme. Set `Z_U = U ×_X Z`,
which is a locally closed subscheme of `U`. Then `C_{Z/X}|_{Z_U} = C_{Z_U/U}`
canonically and functorially in `U`. The identification is the isomorphism
`Hom.Conormal.restrictEtale` of quasi-coherent `𝒪_{Z_U}`-modules, with
`Z_U` realised as `pullback i φ` and restriction as `Modules.pullback` along
`Hom.Conormal.toZ`. -/
@[stacks 04CO]
#check (AlgebraicGeometry.AlgebraicSpace.Hom.Conormal.restrictEtale :
  ∀ {S : Scheme.{u}} {Z X : AlgebraicSpace S} (i : Z ⟶ X) [IsImmersion i]
    {U : Over S} (φ : ofOver U ⟶ X) [Etale φ],
    (Modules.pullback (Hom.Conormal.toZ i φ)).obj (Hom.conormalSheaf i) ≅
      Hom.conormalSheaf (Hom.Conormal.ι i φ))


#check (AlgebraicGeometry.AlgebraicSpace.Hom.Conormal.instIsScheme_space :
  ∀ {S : Scheme.{u}} {Z X : AlgebraicSpace S} (i : Z ⟶ X) [IsImmersion i]
    {U : Over S} (φ : ofOver U ⟶ X) [Etale φ], IsScheme (Hom.Conormal.space i φ))

section

variable {S : Scheme.{u}} {Z X : AlgebraicSpace S} (i : Z ⟶ X) [IsImmersion i]
variable {U : Over S} (φ : ofOver U ⟶ X) [Etale φ]

#check (AlgebraicGeometry.AlgebraicSpace.isImmersion_pullback_snd i φ :
  IsImmersion (Hom.Conormal.ι i φ))

end

#check (AlgebraicGeometry.AlgebraicSpace.Hom.Conormal.restrictEtale_natural :
  ∀ {S : Scheme.{u}} {Z X : AlgebraicSpace S} (i : Z ⟶ X) [IsImmersion i]
    {U : Over S} (φ : ofOver U ⟶ X) [Etale φ]
    {V : Over S} (ψ : ofOver V ⟶ X) [Etale ψ] (f : ofOver U ⟶ ofOver V)
    (hf : f ≫ ψ = φ),
    (Modules.pullback (Hom.Conormal.spaceMap i φ ψ f hf)).map
        (Hom.Conormal.restrictEtale i ψ).hom ≫
        Hom.Conormal.map (Hom.Conormal.chartSq i φ ψ f hf) =
      (Hom.Conormal.restrictEtaleToZReassoc i φ ψ f hf).hom ≫
        (Hom.Conormal.restrictEtale i φ).hom)

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Proetale.ChosenPresentation.SmallToBig.Sections

/-!
# Lemma 61.16.3

The inverse image along `π_S` is computed by global sections of the small
pro-étale inverse image, and is an fpqc sheaf on the chosen slice.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry
open scoped MorphismOfTopoiIn

universe u v w

namespace AlgebraicGeometry.ChosenBigProetaleSite

open SmallToBig

/- Lemma 61.16.3: the big inverse image is computed by small-site global
sections and satisfies fpqc descent. -/
@[stacks 0F65] #check
  (AlgebraicGeometry.ChosenBigProetaleSite.siteMorphismInverseImage_objIso :
    ∀ {X : ChosenBigProetaleSite.{u, v}}
    {S T : X.carrier} (f : T ⟶ S)
    [UnivLE.{max u v, w}]
    [HasWeakSheafify (bigTopology X S) (Type w)]
    [HasWeakSheafify (smallTopology X T) (Type w)]
    (F : Sheaf (smallTopology X S) (Type w)),
    (((siteMorphismOfTopoi X S)⁻¹).obj F).1.obj (op (Over.mk f)) ≅
      (((smallMorphism f)⁻¹).obj F).1.obj (op (smallTerminalObject X T)))

#check
  (AlgebraicGeometry.ChosenBigProetaleSite.siteMorphismInverseImage_isSheaf_fpqc :
    ∀ {X : ChosenBigProetaleSite.{u, v}}
    (S : X.carrier) [UnivLE.{max u v, w}]
    [HasWeakSheafify (bigTopology X S) (Type w)]
    (F : Sheaf (smallTopology X S) (Type w)),
    Presheaf.IsSheaf
      ((Over.post X.toScheme).restrictedTopology
        (Scheme.fpqcTopology.over (X.toScheme.obj S)))
      (((siteMorphismOfTopoi X S)⁻¹).obj F).1)

end AlgebraicGeometry.ChosenBigProetaleSite

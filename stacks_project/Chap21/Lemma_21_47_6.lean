module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Perfect.Triangulated
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 21.47.6

The triangulated perfectness API is owned by `RingedSite.Hom.ModuleDerived`; this file is only its
tagged Chapter 21 source entry.
-/

/- Lemma 21.47.6 (08G9): perfect objects in `D(𝒪_X)` form a triangulated object property; hence
in a distinguished triangle, perfectness of any two objects implies perfectness of the third. -/
@[stacks 08G9] #check @RingedSite.Hom.ModuleDerived.isPerfect_isTriangulated

#check @RingedSite.Hom.ModuleDerived.isPerfect_obj₃_of_distinguished_triangle
#check @RingedSite.Hom.ModuleDerived.isPerfect_obj₂_of_distinguished_triangle
#check @RingedSite.Hom.ModuleDerived.isPerfect_obj₁_of_distinguished_triangle

end

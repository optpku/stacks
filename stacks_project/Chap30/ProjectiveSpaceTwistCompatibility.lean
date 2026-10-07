import ReasLib.AlgebraicGeometry.ProjectiveSpace.GradedPieces
import ReasLib.AlgebraicGeometry.RingedSpace.Module.Cohomology.Map

open AlgebraicGeometry

namespace AlgebraicGeometry

/- Historical Chapter 30 index: standard projective-space data is owned by
`ProjectiveSpace.Basic` and `ProjectiveSpace.GradedPieces`; module-sheaf cohomology and its maps
are owned by `RingedSpace.moduleCohomology` and `RingedSpace.moduleCohomologyMap`. -/

#check projectiveSpaceGrading
#check projectiveSpace
#check projectiveSpaceGradedPiece
#check projectiveSpaceTopCohomologyDual
#check @RingedSpace.moduleCohomology
#check @RingedSpace.moduleCohomologyMap

end AlgebraicGeometry

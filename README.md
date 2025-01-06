# Convex Analysis Geometry Environment

# Installation

**Developers**: A specific installation/usage workflow is recomemded for development, additional details can be found [on the wiki page](https://gitlab.com/clintg105/cage/-/wikis/home/development-workflow).

**Users**: Select one of the two installation methods below.

## One-Shot
```
PacletInstall["ConvexAnalysisGeometry", "Site" -> "http://www.gitlab.com/clintg105/cage/-/raw/main"]
```
## Register for further update
Register site (only needed once):
```
PacletSiteRegister["http://www.gitlab.com/clintg105/cage/-/raw/main"]
```
Install or update:
```
PacletInstall["ConvexAnalysisGeometry"]
```
# Basic Usage

At the start of each Mathematica session:
```
<< ConvexAnalysisGeometry`
```
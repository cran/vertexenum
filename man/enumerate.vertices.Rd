\name{enumerate.vertices}
\alias{enumerate.vertices}
\title{Enumerate the vertices of a polytope.}
\usage{
enumerate.vertices(A, b, warn_if_open=FALSE)
}
\arguments{
  \item{A}{An \code{m} by \code{n} matrix.}
  \item{b}{A \code{m} by \code{1} vector.}
  \item{warn_if_open}{Boolean.}
}
\value{
  A \code{d} by \code{n + 1} dimensional matrix. The rows of this matrix
  represent the \code{d} vertices of the polytope represented by
  the system \code{Ax <= b}. If the optional argument warn_if_open is
  set to TRUE, then a warning will be printed if the system of
  inequalities is not closed, i.e. if it contains an extreme ray.
}
\description{
  Returns a \code{d} by \code{n + 1} dimensional matrix representing the
  \code{d} vertices of the polytope represented by \code{Ax <= b}.
}
\note{
  This is a port of the lrs library for vertex enumeration
  (\url{http://cgm.cs.mcgill.ca/~avis/C/lrs.html}). The source
  was written by David Avis.
}
\examples{
## example vertex enumeration
## the system Ax <= b represents a unit square, with
## the lower left corner at the origin

A <- rbind(c(-1, 0), c(0, 1), c(1, 0), c(0, -1))
b <- c(0, 1, 1, 0)
## outputs a 4 x 2 matrix, each row corresponds to a vertex
enumerate.vertices(A, b)

## second example
## this is a unit square, with lower left corner at the origin, missing
## a facet on the right side
A <- rbind(c(-1, 0), c(0, 1), c(0, -1))
b <- c(0, 1, 0)

## outputs a 2 x 2 matrix, each row corresponds to a vertex
## will print a warning, since the input set described by Ax <= b
## is not closed
enumerate.vertices(A, b, warn_if_open=TRUE)

}
\author{
  Robert Robere \email{robere@cs.toronto.edu}
}
\keyword{geometry}

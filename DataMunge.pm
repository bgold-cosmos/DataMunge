=pod
=head1 NAME

DataMunge - for mathematically manipulating data files

=head1 SYNOPSIS

   use DataMunge;

   $a = DataMunge->loadFromFile("foo.data");
   $b = DataMunge->loadFromFile("bar.data");
   $c = $b - $a;
   $d = $a->clone();
   $d->stretch(1.2);

   $e = performExpr("#1 * sin(#2) ** #3", $a,$b,$c);

=head1 REQUIRES

Perl5?

=head1 EXPORTS

Nothing

=head1 DESCRIPTION

DataMunge provides an interface for dealing with multicolumn data files
where the columns are formatted as:

   x y1 y2 y3 ... yn

i.e. the first column is an independent variable that the other columns are
thought to be functions of.  If you have data in several different files
that you want to combine, DataMunge might be for you.  For example, suppose
you have a file 'a.dat':

   1 10
   2 13
   3 14

and a file 'b.dat':

   1 12
   2 10
   3 8

which you want to add together to get:

   1 22
   2 23
   3 22

With DataMunge, this is as easy as

   $a = DataMunge->loadFromFile("a.dat");
   $b = DataMunge->loadFromFile("b.dat");
   $c = $a+$b;
   $c->saveToFile("c.dat");

What if the x-values in a.dat and b.dat don't quite match?  Upon
encountering an expression like "$a+$b" DataMunge will automatically use
spline interpolation to get the y-values for $b at x-values that match those
in $a.

=head1 METHODS

=head2 Class methods

make() - generic constructor
loadFromFile("$filename") - constructor from a file

=head2 Instance methods

clone() - returns a copy
saveToFile("$filename") - output to $filename
stretch($val) - stretch (multiply) x-values by $val
findLocalMaxInColumn($col) - returns reference to array of x,y pairs of local
   maxima in column $col
findMaxInColumn($col) - returns reference to a single x,y pair of maximum in
   column $col
resizeToMatch($a) - uses interpolation to match x-values of caller to match $a
   implicitly called by most binary operators
performExpr("$expr", $a, $b, $c, ...) - uses 'eval' to perform the expression
   $expr on each column of the other arguments, substituting $a for #1, $b for
   #2, etc... see synopsis for an example

=head2 Overloaded operators

+,-,*,/ - these return a reference to a new object which can be assigned as
   you'd expect.  For more general operations use the method performExpr()
   
=cut

package DataMunge;

use Carp;
use vars qw($VERSION $debug);
use strict;

use overload 
   '+' => 'add',
   '-' => 'subtract',
   '*' => sub { return _performOp($_[0],$_[1],$_[2],'*'); },
   '/' => sub { return _performOp($_[0],$_[1],$_[2],'/'); };


$VERSION = 0.5;
$debug = 0;

# usage: $yout = makeSpline($x,$y,$xout)
# where all the scalars are actually array references
# @$x and @$y represent some function y(x), and you want a different "sampling"
# @$xout, then the subroutine calculates @$yout using cubic interpolation
# optional additional arguments can be used to specify first derivatives
# at the beginning and end (otherwise, zero -second- derivative is assumed)
sub makeSpline {
   croak("not enough arguments to makeSpline") unless (@_ >= 3);
   my($x,$y,$xout) = ($_[0], $_[1], $_[2]);
   my($yout) = [ ];
   $#$yout = $#$xout;
   my($dyl,$dyr) = ($_[3], $_[4]);
   
# make 2nd derivs first
   my(@y2,@u,$s,$p);
   $#y2 = $#$y;
   $#u = $#y2 - 1;

# boundary condition on left side
   if (defined $dyl) {
      $y2[0] = -0.5;
      $u[0] = (3.0 / ($x->[1] - $x->[0]));
      $u[0] *= (($y->[1] - $y->[0]) / ($x->[1] - $x->[0]) - $dyl);
   } else {
      $y2[0] = 0;
      $u[0] = 0;
   }

   my($i);
   for $i (1 .. scalar(@$x)-2) {
      $s = ($x->[$i] - $x->[$i-1]) / ($x->[$i+1] - $x->[$i-1]);
      $p = $s * $y2[$i-1] + 2.0;
      $y2[$i] = ($s - 1.0) / $p;
      $u[$i] = ($y->[$i+1] - $y->[$i]) / ($x->[$i+1] - $x->[$i]);
      $u[$i] -= ($y->[$i] - $y->[$i-1]) / ($x->[$i] - $x->[$i-1]);
      $u[$i] = (6.0*$u[$i] / ($x->[$i+1] - $x->[$i-1]) - $s*$u[$i-1] )/$p;
   }
# boundary condition on right side
   if (defined $dyr) {
      my($xu,$xpu,$yu,$ypu) = ($x->[$#$x], $x->[$#$x-1], $y->[$#$y]
            , $y->[$#$y-1]);
      $y2[$#y2] = (3.0/($xu - $xpu)) * ($dyr-($yu-$ypu)/($xu-$xpu));
      $y2[$#y2] -= 0.5 * $u[$#$x-1];
      $y2[$#y2] /= 0.5 * $y2[$#y2-1] + 1.0;
   } else {
      $y2[$#y2] = 0;
   }

   for ($i=$#y2-1; $i>=0; $i--) {
      $y2[$i] = $y2[$i] * $y2[$i+1] + $u[$i];
   }

# done with 2nd derivs, now make second function using interpolation
# not the most optical search method, but often better than bisection search
# each time
   my($xint,$yint);
   my($k,$h,$b,$a);
   if ($debug) {
      carp "extrapolating outside region, probably garbage"
         if ($xout->[0] < $x->[0] or $xout->[$#$xout] > $x->[$#$x]);
   }
   $k=0;
   for $i (0 .. scalar(@$xout)-1) {
      $xint = $xout->[$i];
      while ( $x->[$k+1] < $xint ) {
         last if ($k == ($#$x - 1));
         $k++;
      }

      $h = $x->[$k+1] - $x->[$k];
      croak("Bad input array") if ($h == 0.0);
      $a = ($x->[$k+1] - $xint) / $h;
      $b = ($xint - $x->[$k]) / $h;
      $yint = $a * $y->[$k] + $b * $y->[$k+1];
      $yint += ( ($a**3 - $a) * $y2[$k] + ($b**3 - $b) * $y2[$k+1] ) *
         ($h*$h) / 6.0;
      $yout->[$i] = $yint;
   }
   return $yout;
}

# constructor with optional filename
sub make {
   my ($this, $filename) = @_;
   my $class = ref($this) || $this;
   my $self = [ ];
   bless $self, $class;
   $self->loadFromFile($filename) if defined $filename;
   return $self;
}

# makes a new copy of the caller
sub clone {
   my $self = shift;
   my $new = $self->make();
   my ($col);
   for $col (0 .. $#$self) {
      $new->copyCol($self, $col);
   }
   return $new;
}      

# loads data from file and can act as constructor
sub loadFromFile {
   croak "loadFromFile expects a filename" if (@_ < 2);
   my ($self, $filename) = @_;
   if (!ref $self) {
      $self = $self->make(); 
   }
   if (!open (IN, $filename)) {
      carp "can't open $filename for loadFromFile";
      return 0;
   }
   my @line;
   my($linenum)=0;
   my($col);
   while (<IN>) {
      next if m/^#/; # skip line if comment
      @line = split;
      for $col (0 .. $#line) {
         $self->[$col][$linenum] = $line[$col];
      }
      $linenum++;
   }
   return $self;
}

# save to file, returns number of lines written
sub saveToFile {
   croak "saveToFile expects a filename" if (@_ < 2);
   my ($self, $filename) = @_;
   if (!open (OUT, ">$filename")) {
      carp "can't open $filename for output ";
      return 0;
   }
   my $numcols = scalar @$self;
   my $numrows = scalar @{$self->[0]};
   my ($row,$col);
   for $row (0 .. $numrows-1) {
      for $col (0 .. $numcols-1) {
         print OUT $self->[$col][$row];
         print OUT "  ";
      }
      print OUT "\n";
   }
   return $numrows;
}

# accessor method, rarely used unfortunately
sub col {
   return ($_[0]->[$_[1]]);
}

# copies a column of data, mainly used by other methods
sub copyCol {
   croak "copycol needs two arguments" if (@_ < 3);
   my ($self, $from, $colnum) = @_;
   $self->[$colnum] = [@{$from->[$colnum]}];
   return $self;
}

# stretches x values by the argument
sub stretch {
   my($self, $stretch) = @_;
   my $row;
   for $row (0 .. $#{$self->[0]} ) {
      $self->[0][$row] *= $stretch;
   }
   return $self;
}

# stretches with area conservation
sub conserveStretch {
   my($self, $stretch) = @_;
   my($row,$col);
   my $numcols = scalar @$self;

   for $row (0 .. $#{$self->[0]} ) {
      $self->[0][$row] *= $stretch;
      for $col (1 .. $numcols-1) {
         $self->[$col][$row] /= $stretch;
      }
   }
   return $self;
}

sub _fitPeakAround {
# the following looks like rather a mess, but it's really a parabolic fit
   my($self, $col, $maxrow) = @_;
   my($x1,$x2,$x3,$y1,$y2,$y3) = 
      ($self->[0][$maxrow-1],
       $self->[0][$maxrow],
       $self->[0][$maxrow+1],
       $self->[$col][$maxrow-1],
       $self->[$col][$maxrow],
       $self->[$col][$maxrow+1]);
   my($denom) = 2 * ($x1*($y2-$y3) + $x2*($y3-$y1) + $x3*($y1-$y2));
   my($xmax) = ($x1**2)*($y2-$y3) + ($x2**2)*($y3-$y1) + ($x3**2)*($y1-$y2);
   $xmax /= $denom;
   my($ymax) = $y1*($x2-$x3)**2 - $y2*($x1-$x3)**2;
   $ymax *= $ymax;
   $ymax -= 2*(($x1-$x2)**2) * ($y1*($x2-$x3)**2 + $y2*($x1-$x3)**2) * $y3;
   $ymax += ($y3**2) * ($x1-$x2)**4;
   $ymax /= $denom;
   $ymax /= 2*($x1-$x2)*($x1-$x3)*($x2-$x3);
   return( [ $xmax, $ymax ] );
}

sub findLocalMaxInColumn {
   my($self, $col) = @_;
   my $row;
   my $deriv = -9e99;
   my $lastDeriv = -9e99;
   my @peaks;
   for $row (2 .. $#{$self->[$col]} ) {
      $deriv = $self->[$col][$row] - $self->[$col][$row-1];
      $lastDeriv = $self->[$col][$row-1] - $self->[$col][$row-2];
      if ($deriv <= 0 and $lastDeriv > 0) {
         push(@peaks,  $self->_fitPeakAround($col,$row-1));
      }
   }
   return(\@peaks);
}

sub findMaxInColumn {
   my($self, $col) = @_;
   my $row;
   my $max = -9e99;
   my $maxrow;
   for $row (0 .. $#{$self->[$col]} ) {
      if ($self->[$col][$row] > $max) {
         $max = $self->[$col][$row];
         $maxrow = $row;
      }
   }
# the following looks like rather a mess, but it's really a parabolic fit
   my($x1,$x2,$x3,$y1,$y2,$y3) = 
      ($self->[0][$maxrow-1],
       $self->[0][$maxrow],
       $self->[0][$maxrow+1],
       $self->[$col][$maxrow-1],
       $self->[$col][$maxrow],
       $self->[$col][$maxrow+1]);
   my($denom) = 2 * ($x1*($y2-$y3) + $x2*($y3-$y1) + $x3*($y1-$y2));
   my($xmax) = ($x1**2)*($y2-$y3) + ($x2**2)*($y3-$y1) + ($x3**2)*($y1-$y2);
   $xmax /= $denom;
   my($ymax) = $y1*($x2-$x3)**2 - $y2*($x1-$x3)**2;
   $ymax *= $ymax;
   $ymax -= 2*(($x1-$x2)**2) * ($y1*($x2-$x3)**2 + $y2*($x1-$x3)**2) * $y3;
   $ymax += ($y3**2) * ($x1-$x2)**4;
   $ymax /= $denom;
   $ymax /= 2*($x1-$x2)*($x1-$x3)*($x2-$x3);
   return( [ $xmax, $ymax ] );


=pod

# the following uses splines to find the maximum, but fitting a parabola is
# probably better in the end.
   my(@newi,$i);
   for $i (0 .. 20) {
      $newi[$i] = $maxrow-2 + $i/5;
   }
   my($newx) = makeSpline([0 .. $#{$self->[0]}], $self->[0], \@newi);
   my($newy) = makeSpline($self->[0], $self->[$col], $newx);
   for $i (0 .. 20) {
      if ($newy->[$i] > $max) {
         $max = $newy->[$i];
         $maxrow = $i;
      }
   }
   return( [$newx->[$maxrow], $max] );

=cut

}

# finds average X given weights in Y
sub averageWithWeight {
   croak "averageWithWeight needs an argument" if (@_ < 2);
   my($self, $col) = @_;
   my($i);
   my($sum, $weight) = (0, 0);

   for $i (0 .. $#{$self->[0]}) {
      $sum += $self->[0][$i] * $self->[$col][$i];
      $weight += $self->[$col][$i];
   }
   return $sum/$weight;
}

# reassigns x values in the caller so they match those in the argument
sub resizeToMatch {
   croak "resize needs an argument" if (@_ < 2);
   my ($self, $goal) = @_;

   my ($col, $colref,$newcolref);
   for $col (1 .. (scalar @$goal)-1 ) {
      $colref = $self->[$col];
      $newcolref = makeSpline($self->[0], $colref, $goal->[0]);
      $self->[$col] = $newcolref;
   }
   $self->copyCol($goal,0);
   return $self;
}

# this is used for the meat of binary arithmetic operations
# handles + - * /
sub _performOp {
   my ($a,$b,$switch,$op) = @_;
   my ($row, $col, $result);
   
   if (ref $b) { # both arguments are objects
      $result = $a->make();
      $result->copyCol($a,0);
      for $col (1 .. $#$a) {
         # result is set to $b here!
         $result->[$col] = makeSpline($b->[0], $b->[$col], $a->[0]);
         for $row (0 .. $#{$a->[$col]}) {
            $result->[$col][$row] += $a->[$col][$row] if ($op eq '+');
            $result->[$col][$row] *= $a->[$col][$row] if ($op eq '*');
            $result->[$col][$row] = $a->[$col][$row] - $result->[$col][$row]
               if ($op eq '-');
            $result->[$col][$row] = $a->[$col][$row] / $result->[$col][$row]
               if ($op eq '/');
         }
      }
   } else { # second argument is a scalar
      $result = $a->clone();
      for $col (1 .. $#$a) {
         for $row (0 .. $#{$a->[$col]}) {
            $result->[$col][$row] += $b if ($op eq '+');
            $result->[$col][$row] *= $b if ($op eq '*');
            if ($op eq '-') {
               $result->[$col][$row] -= $b;
               $result->[$col][$row] = -($result->[$col][$row]) if $switch;
            }
            if ($op eq '/') {
               $result->[$col][$row] /= $b;
               $result->[$col][$row] = (1.0 / $result->[$col][$row]) if $switch;
            }
         }
      }
   }
   return $result;
}            

# overloaded math, these pass off most of the work to _performOp
sub add {
   my ($a, $b, $switch) = @_;
   return $a unless (defined $b); # unary +
   return _performOp($a,$b,$switch,'+');
}

sub subtract {
   my ($a, $b, $switch) = @_;
   return($a * -1) unless (defined $b); # unary -
   return _performOp($a,$b,$switch,'-');
}

sub multiply { return _performOp($_[0],$_[1],$_[2],'*'); }
sub divide { return _performOp($_[0],$_[1],$_[2],'/'); }

# uses eval, potentially really slow
# doesn't modify the calling object (which could just be a class)
sub performExpr {
   my ($self, $expr, @vars) = @_;
   my ($i, $col, $row, $var, @newvars, $search, $replace, $loopexpr);
   my $result = $self->make();
   
   $newvars[0] = $vars[0];
   for $i (1 .. $#vars) {
      $newvars[$i] = $vars[$i]->clone();
      $newvars[$i]->resizeToMatch($vars[0]);
   }
   
   $result->copyCol($vars[0],0);
   for $col (1 .. $#{$newvars[0]}) {
      for $row (0 .. $#{$newvars[0]->[$col]}) {
         $i = 1;
         $loopexpr = $expr;
         for $var (@newvars) {
            $search = "#$i";
            $replace = $var->[$col][$row];
            $loopexpr =~ s/$search/$replace/g;
            $i++;
         }
         if ($debug && $row == 0) {
            carp "expr for row 0 of column $col is: $loopexpr";
         }
         $result->[$col][$row] = eval $loopexpr;
      }
   }
   return $result;
}

1;

/*-
 * APT - Analysis of Petri Nets and labeled Transition systems
 * Copyright (C) 2018-2019  Harro Wimmel
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License along
 * with this program; if not, write to the Free Software Foundation, Inc.,
 * 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA.
 */

package uniol.apt.relabelling;

import java.util.Map;
import java.util.HashMap;
import java.util.Set;
import java.util.HashSet;

public class BaseTransform {
	public final int dimension;
	public final long[][][] coefficient;
	public int used;
	public boolean[] baseindex;

	public BaseTransform(int dim) {
		dimension = dim;
		coefficient = new long[dimension][dimension][2];
		baseindex = new boolean[dimension];
		clear();
	}

	public void clear() {
		for(int i=0; i<used; i++) baseindex[i] = false;
		used = 0;
		for(int i=0; i<dimension; i++)
			for(int j=0; j<dimension; j++)
				coefficient[i][j][1]=1;
	}

	public long gcd(long a, long b) {
		if (b == 0) return a;
		return gcd(b, a%b);
	}

	public long[][] transform(Map<Integer,Integer> pv) {
		long[][] value = new long[dimension][2];
		for(int i=0; i<dimension; i++) {
			if (pv.containsKey(i)) value[i][0] = pv.get(i);
			else value[i][0] = 0;
			value[i][1] = 1;
			long[][] iptr = coefficient[i];
			for(Map.Entry<Integer,Integer> me : pv.entrySet()) {
				long[] ptr = iptr[me.getKey()];
				if (ptr[0]!=0 && me.getValue()!=0) {
					long comden = gcd(ptr[1],value[i][1]);
					long denom = (value[i][1]/comden)*ptr[1];
					long num = value[i][0]*(ptr[1]/comden)+ptr[0]*me.getValue()*(value[i][1]/comden);
					if (num==0L) { denom=1L; comden=1L; }
					else comden = gcd(num, denom); 
					value[i][0] = num/comden; 
					value[i][1] = denom/comden;
				}
			}
		}
		return value;
	}

	public boolean add(Map<Integer,Integer> pv) {
		long value[][] = transform(pv);
		int row = minRow(value);
		if (row < 0) return false; // linear dependence
		// new base vector found
		diagonalise(value, row);
		baseindex[row] = true;
		return true;
	}

	public int minRow(long[][] value) {
		long max = Long.MAX_VALUE;
		int row = -1;
		for(int i=0; i<dimension; i++) {
			if (value[i][0] != 0L && !baseindex[i] && max > value[i][0] && max > value[i][1]) {
				max = value[i][0];
				if (max < value[i][1]) max = value[i][1];
				row = i;
			}
		}
		return row;
	}

	public void diagonalise(long[][] value, int row) {
		for(int i=0; i<dimension; i++)
			if (row != i && value[i][0] != 0L) {
				long cden1 = gcd(value[i][0],value[row][0]);
				long cden2 = gcd(value[i][1],value[row][1]);
				long num = -(value[i][0]/cden1)*(value[row][1]/cden2);
				long denom = (value[row][0]/cden1)*(value[i][1]/cden2);
				cden1 = gcd(coefficient[i][row][1],denom);
				num = num*(coefficient[i][row][1]/cden1)+coefficient[i][row][0]*(denom/cden1);
				denom *= (coefficient[i][row][1]/cden1);
				cden1 = gcd(num,denom);
				coefficient[i][row][0] = num/cden1;
				coefficient[i][row][1] = denom/cden1;
			}
	}
}

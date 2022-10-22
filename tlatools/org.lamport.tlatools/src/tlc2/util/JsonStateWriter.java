/*******************************************************************************
 * Copyright (c) 2016 Microsoft Research. All rights reserved. 
 *
 * The MIT License (MIT)
 * 
 * Permission is hereby granted, free of charge, to any person obtaining a copy 
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies
 * of the Software, and to permit persons to whom the Software is furnished to do
 * so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software. 
 * 
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN
 * AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
 * WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 * Contributors:
 *   Markus Alexander Kuppe - initial API and implementation
 ******************************************************************************/

package tlc2.util;

import tlc2.module.Json;
import tlc2.tool.TLCState;

import java.io.IOException;
import java.util.stream.Collectors;

public class JsonStateWriter extends StateWriter {

	public JsonStateWriter(final String fname) throws IOException {
		super(fname);
		this.writer.append("[\n");
	}

	/* (non-Javadoc)
	 * @see tlc2.util.StateWriter#writeState(tlc2.tool.TLCState)
	 */
	public synchronized void writeState(final TLCState state) {
		this.writer.append(state.getVals().entrySet().stream().map(e -> {
			try {
				return String.format("{\"%s\": %s}", e.getKey(), Json.getNode(e.getValue()));
			} catch (IOException ex) {
				throw new RuntimeException(ex);
			}
		}).collect(Collectors.joining(",")));

		this.writer.append(",\n");
	}

	/* (non-Javadoc)
	 * @see tlc2.util.IStateWriter#close()
	 */
	public void close() {
		this.writer.append("]");
		super.close();
	}
}

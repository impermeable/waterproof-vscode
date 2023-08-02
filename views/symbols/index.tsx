import React from "react";
import { createRoot } from "react-dom/client";

import "../styles/index.css";
// get the react panel
import Symbols from "./symbols";

const container = document.getElementById("root");
// createRoot(container!) if you use TypeScript
const root = createRoot(container!); 
// render the symbols panel
root.render(
    <React.StrictMode>
        <Symbols />
    </React.StrictMode>
);